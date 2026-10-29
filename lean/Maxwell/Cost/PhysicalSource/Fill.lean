import Maxwell.Cost.PhysicalSource.Footprint
import Maxwell.Cost.PhysicalMaterial.DenseFill
import Maxwell.Cost.PhysicalEmit.For

/-! Every source-overlay entry is initialized by an actual counted loop,
starting with its arbitrary old memory contents. -/
namespace Maxwell.Cost.PhysicalSource.Overlay
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

structure InitFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ j, j=4 ∨ 10≤j → j≠37 → j≠333 → j≠338 → t.tapes j=s.tapes j

theorem InitFrame.refl (s : BitRAMState) : InitFrame s s := ⟨rfl,rfl,rfl,fun _ _ _ _ _ => rfl⟩
theorem InitFrame.trans {s t u : BitRAMState} (h : InitFrame s t) (k : InitFrame t u) : InitFrame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun j hj h37 h333 h338 => (k.tapes j hj h37 h333 h338).trans (h.tapes j hj h37 h333 h338)⟩

def filled {n : ℕ} (words : Fin 3 → Vector (List Bool) n) (port : Fin 3)
    (bits : List Bool) (k : ℕ) : Fin 3 → Vector (List Bool) n :=
  Function.update words port (PhysicalMaterial.Dense.filled (words port) bits k)

@[simp] theorem filled_zero {n : ℕ} (words : Fin 3 → Vector (List Bool) n)
    (port : Fin 3) (bits : List Bool) : filled words port bits 0 = words := by
  simp [filled]

theorem filled_step {n : ℕ} (words : Fin 3 → Vector (List Bool) n)
    (port : Fin 3) (bits : List Bool) (i : Fin n) :
    Function.update (filled words port bits i.val) port
      ((filled words port bits i.val port).set i bits) = filled words port bits (i.val+1) := by
  simp only [filled,Function.update_self,Function.update_idem]
  rw [PhysicalMaterial.Dense.filled_step]

@[simp] theorem filled_all {n : ℕ} (words : Fin 3 → Vector (List Bool) n)
    (port : Fin 3) (bits : List Bool) : filled words port bits n =
      Function.update words port (Vector.replicate n bits) := by simp [filled]

def fillCode (port : Fin 3) : Code := PhysicalEmit.forCode 337 338 333 (writeCode port)

private def Invariant {n : ℕ} (l : Layout n) (words : Fin 3 → Vector (List Bool) n)
    (port : Fin 3) (v : ℕ) (initial : BitRAMState) (k : ℕ) (s : Store) : Prop :=
  Ready s.val ∧ Blank s.val 37 ∧
    Stored l (filled words port (FixedWidth.bits (addressValue l.width) v.bits) k) s.val ∧
    Word s.val (valueTape port) v ∧ InitFrame initial s.val ∧ Outside l initial s.val

private theorem invariant_stable {n : ℕ} (l : Layout n) (words : Fin 3 → Vector (List Bool) n)
    (port : Fin 3) (v : ℕ) (initial : BitRAMState) (k : ℕ) (s t : Store)
    (hf : PhysicalEmit.LoopFrame {338,333} s.val t.val)
    (hs : Invariant l words port v initial k s) : Invariant l words port v initial k t := by
  obtain ⟨hr,h37,hd,hv,hi,ho⟩ := hs
  have keep (j : ℕ) (h338 : j≠338) (h333 : j≠333) : t.val.tapes j=s.val.tapes j :=
    hf.tapes j (by simp [h338,h333])
  refine ⟨(fun j hj => blank_of_eq (keep j (by omega) (by omega)) (hr j hj)),
    blank_of_eq (keep 37 (by decide) (by decide)) h37,
    ⟨BankArray.word_of_eq (keep 300 (by decide) (by decide)) hd.width,
      BankArray.word_of_eq (keep 301 (by decide) (by decide)) hd.clock,
      fun j => BankArray.word_of_eq (keep (baseTape j)
        (by have := j.isLt; dsimp [baseTape]; omega)
        (by have := j.isLt; dsimp [baseTape]; omega)) (hd.bases j),
      fun j => by simpa only [hf.memory] using hd.arrays j⟩,
    word_of_eq (keep (valueTape port) (by have := port.isLt; dsimp [valueTape]; omega)
      (by dsimp [valueTape]; omega)) hv,
    hi.trans ⟨hf.inputHead,hf.randomCursor,hf.output,fun j _ _ h333 h338 => keep j h338 h333⟩,
    ho.trans (Outside.of_memory l hf.memory)⟩

/-- Initialize one complete source array using its stored edge count. The
same finite loop serves positive, negative and denominator arrays. -/
theorem fill {n : ℕ} (l : Layout n) (words : Fin 3 → Vector (List Bool) n)
    (port : Fin 3) (v B : ℕ) (hl : l.Sized B) (hn : n.bits.length≤B)
    (hfit : v.bits.length≤addressValue l.width)
    (input : List Bool) (tape : ℕ→Bool) (oldIndex : ℕ) (oldCount : List Bool)
    (hiB : oldIndex.bits.length≤B) (hcB : oldCount.length≤B) (s : Store)
    (hs : Ready s.val) (h37 : Blank s.val 37) (hd : Stored l words s.val)
    (hv : Word s.val (valueTape port) v) (hcount : Word s.val 337 n)
    (hc : BankArray.Word s.val 338 oldCount) (hi : Word s.val 333 oldIndex) :
    ∃ cost t finalCount, cost≤50000*(n+1)*(B+2)^2 ∧
      Executes input tape (fillCode port) cost s t ∧ Ready t.val ∧ Blank t.val 37 ∧
      Stored l (Function.update words port
        (Vector.replicate n (FixedWidth.bits (addressValue l.width) v.bits))) t.val ∧
      Word t.val (valueTape port) v ∧ Word t.val 333 n ∧
      BankArray.Word t.val 338 finalCount ∧ finalCount.length=n.bits.length ∧ InitFrame s.val t.val ∧ Outside l s.val t.val := by
  let P := Invariant l words port v s.val
  have body : ∀ i, i<n → ∀ u, P i u → Word u.val 333 i →
      ∃ cost t, cost≤40000*(B+2)^2 ∧ Executes input tape (writeCode port) cost u t ∧
        P (i+1) t ∧ t.val.tapes 333=u.val.tapes 333 ∧ t.val.tapes 338=u.val.tapes 338 := by
    intro i hin u hu hindex
    obtain ⟨hur,hu37,hud,huv,huf,huo⟩ := hu
    have hil : i.bits.length≤B := by
      rw [Nat.size_eq_bits_len] at hn ⊢
      exact (Nat.size_le_size hin.le).trans hn
    obtain ⟨c,t,hc,he,htr,ht37,htd,hm,hf⟩ := write l _ port ⟨i,hin⟩ v B hl hfit
      input tape i.bits (addressValue_bits i) hil u hur hu37 hud hindex huv
    have frame : InitFrame u.val t.val :=
      ⟨hf.1,hf.2.1,hf.2.2.1,fun j hj hj37 _ _ => hf.2.2.2.1 j hj hj37⟩
    refine ⟨c,t,hc,he,⟨htr,ht37,?_,word_of_eq (hf.2.2.2.1 (valueTape port)
      (by right; dsimp [valueTape]; omega) (by dsimp [valueTape]; omega)) huv,huf.trans frame,huo.trans (Outside.of_write l port ⟨i,hin⟩ v hm)⟩,
      hf.2.2.2.1 333 (by decide) (by decide),hf.2.2.2.1 338 (by decide) (by decide)⟩
    rw [←filled_step words port _ ⟨i,hin⟩]
    exact htd
  obtain ⟨c,t,fc,hcost,he,ht,hi,hc,hcl⟩ := PhysicalEmit.for_executes 337 338 333 n
    (by decide) (by decide) (by decide) (writeCode port) input tape P (40000*(B+2)^2)
    (invariant_stable l words port v s.val) body oldIndex oldCount s hcount hc hi
    ⟨hs,h37,by simpa using hd,hv,.refl _,.refl _ _⟩
  obtain ⟨htr,ht37,htd,htv,htf,hto⟩ := ht
  refine ⟨c,t,fc,?_,he,htr,ht37,by simpa using htd,htv,hi,hc,hcl,htf,hto⟩
  have hbound : 6*oldIndex.bits.length+6*oldCount.length+15*n.bits.length+25+
      (n+1)*(13*n.bits.length+15)+n*(40000*(B+2)^2+12*n.bits.length+18) ≤
      6*B+6*B+15*B+25+(n+1)*(13*B+15)+n*(40000*(B+2)^2+12*B+18) := by gcongr
  exact hcost.trans (hbound.trans (by nlinarith))

end Maxwell.Cost.PhysicalSource.Overlay
