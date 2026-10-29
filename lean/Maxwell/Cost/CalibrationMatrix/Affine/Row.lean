import Maxwell.Cost.CalibrationMatrix.Affine.RowCore

namespace Maxwell.Cost.CalibrationMatrix.Affine
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1000000

variable {n : ℕ}

def rowCode : Code := .seq rowCoreCode (BankArray.incrementCode 104)

theorem row (d : Data n) (words : Fin 10 → Vector (List Bool) n) (B : ℕ)
    (hd : d.Sized B) (hn : n < 2^B) (i : Fin n)
    (hwp : (newWPositive d words i).bits.length ≤ addressValue d.width)
    (hwn : (newWNegative d words i).bits.length ≤ addressValue d.width)
    (hxp : (newXPositive d words i).bits.length ≤ addressValue d.width)
    (hxn : (newXNegative d words i).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (s : Store) (hr : Ready s.val (dotValues 0 0)) (hdata : Stored d words s.val)
    (hindex : BankArray.Word s.val 104 index) (h37 : Blank s.val 37) :
    ∃ cost t, cost ≤ 2000000*(B+2)^2 ∧ Executes input tape rowCode cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Stored d (rowWords d words i) t.val ∧
      BankArray.Word t.val 104 (Increment.bits index) ∧ (Increment.bits index).length ≤ B ∧
      Blank t.val 37 ∧ t.val.tapes 108 = s.val.tapes 108 ∧
      t.val.memory = rowMemory d words i s.val.memory ∧
      (∀ j, j = 102 ∨ j = 103 ∨ j = 106 → t.val.tapes j = s.val.tapes j) ∧ MatrixFrame s.val t.val := by
  obtain ⟨c, a, hc, ea, har, had, hai, ha37, ha108, ham, hac, haf⟩ :=
    row_core d words B hd i hwp hwn hxp hxn input tape index hi hil s hr hdata hindex h37
  obtain ⟨k, t, hk, et, hti, _, htm, _, keep, ft⟩ := BankArray.increment_bank
    104 (by omega) input tape index a hai har.2.1
  have frame : MatrixFrame a.val t.val :=
    ⟨ft.1, ft.2.1, ft.2.2.1, fun j hj _ _ _ _ h104 _ _ => ft.2.2.2.1 j hj h104,
      ft.2.2.2.2⟩
  refine ⟨c+k, t, ?_, ea.seq et, har.of_tapes (fun j hj => keep j (by omega)),
    had.of_tapes_memory htm (fun j hj => keep j (by omega)), hti, ?_,
    RationalAccumulator.blank_of_eq (keep 37 (by omega)) ha37,
    (keep 108 (by omega)).trans ha108, htm.trans ham, (fun j hj => (keep j (by omega)).trans (hac j hj)), haf.trans frame⟩
  · have hquad : B+2 ≤ (B+2)^2 := by nlinarith
    nlinarith
  · exact BankArray.increment_length_bound index B hil (by rw [hi]; omega)

end Maxwell.Cost.CalibrationMatrix.Affine
