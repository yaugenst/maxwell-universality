import Maxwell.Cost.PhysicalMaterial.Descriptors

namespace Maxwell.Cost.PhysicalMaterial.Descriptors
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

def readCode : Code := .seq (loadCode 0) (.seq (loadCode 1)
  (.seq (loadCode 2) (.seq (loadCode 3) (loadCode 4))))

/-- Five addressed reads load one complete runtime descriptor. -/
theorem read {n : ℕ} (d : Data n) (row : Fin n) (B : ℕ) (hd : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = row.val) (hil : index.length ≤ B) (s : Store)
    (hs : Ready s.val) (hdata : Stored d s.val) (hindex : BankArray.Word s.val 302 index)
    (hbank : Bank s.val (fun _ => 0)) :
    ∃ cost t, cost ≤ 100000 * (B+2)^2 ∧ Executes input tape readCode cost s t ∧
      Ready t.val ∧ Stored d t.val ∧ Bank t.val (value d row) ∧ Frame targets s.val t.val := by
  let v1 := Function.update (fun _ : Fin 5 => 0) 0 (value d row 0)
  let v2 := Function.update v1 1 (value d row 1)
  let v3 := Function.update v2 2 (value d row 2)
  let v4 := Function.update v3 3 (value d row 3)
  obtain ⟨c1, a, hc1, e1, ha, had, hav, fa⟩ := load d row 0 B hd input tape index hi hil
    s hs hdata hindex (fun _ => 0) hbank rfl
  obtain ⟨c2, b, hc2, e2, hb, hbd, hbv, fb⟩ := load d row 1 B hd input tape index hi hil
    a ha had (BankArray.word_of_eq (fa.tapes 302 (by omega) (by decide)) hindex)
    v1 hav (by simp [v1])
  have fab := fa.trans fb
  obtain ⟨c3, c, hc3, e3, hc, hcd, hcv, fc⟩ := load d row 2 B hd input tape index hi hil
    b hb hbd (BankArray.word_of_eq (fab.tapes 302 (by omega) (by decide)) hindex)
    v2 hbv (by simp [v2, v1])
  have fabc := fab.trans fc
  obtain ⟨c4, e, hc4, e4, he, hed, hev, fe⟩ := load d row 3 B hd input tape index hi hil
    c hc hcd (BankArray.word_of_eq (fabc.tapes 302 (by omega) (by decide)) hindex)
    v3 hcv (by simp [v3, v2, v1])
  have fabce := fabc.trans fe
  obtain ⟨c5, t, hc5, e5, ht, htd, htv, ft⟩ := load d row 4 B hd input tape index hi hil
    e he hed (BankArray.word_of_eq (fabce.tapes 302 (by omega) (by decide)) hindex)
    v4 hev (by simp [v4, v3, v2, v1])
  have hvalues : Function.update v4 4 (value d row 4) = value d row := by
    funext i
    fin_cases i <;> simp [v4, v3, v2, v1]
  refine ⟨c1+(c2+(c3+(c4+c5))), t, by omega, e1.seq (e2.seq (e3.seq (e4.seq e5))),
    ht, htd, ?_, fabce.trans ft⟩
  simpa only [hvalues] using htv

theorem value_bits {n : ℕ} (d : Data n) (row : Fin n) (port : Fin 5)
    (s : BitRAMState) (h : Stored d s) :
    (value d row port).bits.length ≤ addressValue d.width := by
  exact (CalibrationMatrix.canonical_length_le _).trans ((h.arrays port).length row).le

end Maxwell.Cost.PhysicalMaterial.Descriptors
