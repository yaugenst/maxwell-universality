import Maxwell.Cost.CalibrationSource.RepackEntry

namespace Maxwell.Cost.CalibrationSource.Repack
open Structured CalibrationMatrix
set_option maxHeartbeats 1200000

def prefixCode {m : ℕ} : (n : ℕ) → n ≤ m → Code
  | 0,_ => .skip
  | n+1,hn => .seq (prefixCode (m := m) n (by omega)) (entryCode n)

def code (m : ℕ) : Code := prefixCode m le_rfl

def costCap (m B : ℕ) : ℕ := 1+m*(122000*(B+2)^2)

private theorem prefix_executes {m : ℕ} (c : Data) (d : ModeRead.Data m) (B : ℕ)
    (hc : c.Sized B) (hd : d.Sized B) (hsep : c.Separated d)
    (hfit : ∀ i a, (d.value i a).bits.length ≤ addressValue c.width)
    (hlen : m.bits.length ≤ B) (initial : Fin 2 → Vector (List Bool) m)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Stored c initial s.val) (hm : ModeRead.Stored readLayout d s.val) (hw : Workspace s.val)
    (n : ℕ) (hn : n ≤ m) :
    ∃ cost t, cost ≤ costCap n B ∧ Executes input tape (prefixCode n hn) cost s t ∧
      Stored c (fun a => GenerationPrefix.written (initial a) (words c d a) n) t.val ∧
      ModeRead.Stored readLayout d t.val ∧ Workspace t.val ∧ Frame s.val t.val ∧
      OutputOutside c.output m (addressValue c.width) s.val t.val := by
  induction n with
  | zero => exact ⟨1,s,by simp [costCap],.skip s,by simpa only [GenerationPrefix.zero] using hs,
      hm,hw,Frame.refl _,OutputOutside.refl _ _ _ _⟩
  | succ n ih =>
    obtain ⟨pc,p,hpc,ep,ps,pm,pw,pf,po⟩ := ih (by omega)
    let i : Fin m := ⟨n,by omega⟩
    have hi : i.val.bits.length ≤ B := by
      have h := Nat.size_le_size (Nat.le_of_lt i.isLt)
      rw [← Nat.size_eq_bits_len,← Nat.size_eq_bits_len] at h
      exact h.trans hlen
    obtain ⟨ec,t,hec,et,ts,tm,tw,tf,tout⟩ := entry c d i B hc hd hsep (hfit i) hi _ input tape p ps pm pw
    refine ⟨pc+ec,t,?_,ep.seq et,?_,tm,tw,pf.trans tf,po.trans tout⟩
    · dsimp only [costCap] at *; nlinarith only [hpc,hec]
    · have hs : (fun a => (GenerationPrefix.written (initial a) (words c d a) n).set i ((words c d a).get i)) =
          (fun a => GenerationPrefix.written (initial a) (words c d a) (n+1)) := by
        funext a
        exact GenerationPrefix.step _ _ i
      exact hs ▸ ts

/-- Repack the retained qhat into actual calibration sparse coefficient
arrays. Their previous contents are arbitrary and do not enter the result. -/
theorem executes {m : ℕ} (c : Data) (d : ModeRead.Data m) (B : ℕ)
    (hc : c.Sized B) (hd : d.Sized B) (hsep : c.Separated d)
    (hwidth : addressValue d.width ≤ addressValue c.width) (hlen : m.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (h100 : BankArray.Word s.val 100 c.width) (h101 : BankArray.Word s.val 101 c.clock)
    (hbases : ∀ a : Fin 2, BankArray.Word s.val (161+a.val) (c.bases a))
    (hm : ModeRead.Stored readLayout d s.val) (hw : Workspace s.val) :
    ∃ cost t, cost ≤ costCap m B ∧ Executes input tape (code m) cost s t ∧
      Stored c (words c d) t.val ∧ ModeRead.Stored readLayout d t.val ∧
      Workspace t.val ∧ Frame s.val t.val ∧ OutputOutside c.output m (addressValue c.width) s.val t.val := by
  have fit (i : Fin m) (a : Fin 2) : (d.value i a).bits.length ≤ addressValue c.width := by
    have hbits : (addressValue ((d.words a).get i)).bits.length ≤ ((d.words a).get i).length := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length _)
    exact hbits.trans (((hm.arrays a).length i).le.trans hwidth)
  let initial := fun a => BitArray.snapshot s.val.memory (addressValue (c.bases a)) (addressValue c.width) m
  obtain ⟨cost,t,hcost,he,hs,htm,htw,hf,ho⟩ := prefix_executes c d B hc hd hsep fit hlen initial
    input tape s ⟨h100,h101,hbases,fun _ => BitArray.snapshot_represents _ _ _ _⟩ hm hw m le_rfl
  exact ⟨cost,t,hcost,he,by simpa only [GenerationPrefix.complete] using hs,htm,htw,hf,ho⟩

/-- Actual stored repacked words decode to the exact shared mode channels. -/
theorem words_value {m : ℕ} (c : Data) (d : ModeRead.Data m) (i : Fin m) (a : Fin 2)
    (hfit : (d.value i a).bits.length ≤ addressValue c.width) :
    addressValue ((words c d a).get i) = d.value i a := by
  rw [words_get,FixedWidth.bits_value _ _ hfit,addressValue_bits]

/-- The charged execution of the compiled finite repacking program. -/
theorem compiled_run {m : ℕ} (c : Data) (d : ModeRead.Data m) (B : ℕ)
    (hc : c.Sized B) (hd : d.Sized B) (hsep : c.Separated d)
    (hwidth : addressValue d.width ≤ addressValue c.width) (hlen : m.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (h100 : BankArray.Word s.val 100 c.width) (h101 : BankArray.Word s.val 101 c.clock)
    (hbases : ∀ a : Fin 2, BankArray.Word s.val (161+a.val) (c.bases a))
    (hm : ModeRead.Stored readLayout d s.val) (hw : Workspace s.val) :
    ∃ t : Store,
      (runPriced ((code m).compile.next input tape) (costCap m B+1) s.val).finished =
        some (t.place (code m).size) ∧
      (runPriced ((code m).compile.next input tape) (costCap m B+1) s.val).instructions ≤ costCap m B ∧
      Stored c (words c d) t.val ∧ ModeRead.Stored readLayout d t.val ∧
      Workspace t.val ∧ Frame s.val t.val ∧ OutputOutside c.output m (addressValue c.width) s.val t.val := by
  obtain ⟨cost,t,hcost,he,hs,htm,htw,hf,ho⟩ := executes c d B hc hd hsep hwidth hlen input tape s h100 h101 hbases hm hw
  have run := he.compiled_run (costCap m B+1) (by omega)
  exact ⟨t,run.1,run.2.symm ▸ hcost,hs,htm,htw,hf,ho⟩

end Maxwell.Cost.CalibrationSource.Repack
