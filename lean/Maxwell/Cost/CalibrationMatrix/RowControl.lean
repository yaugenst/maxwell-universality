import Maxwell.Cost.CalibrationMatrix.Rows

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)

/-- Copy the persistent column count into the expendable inner-loop counter. -/
def rowSetupCode : Code := .call (WordTransfer.clone 107 106)

theorem row_setup (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (s : Store) (hc : BankArray.Word s.val 107 count) (hb : Blank s.val 106) :
    ∃ t, Executes input tape rowSetupCode (15*count.length+17) s t ∧
      BankArray.Word t.val 106 count ∧
      (∀ i, i ≠ 106 → t.val.tapes i = s.val.tapes i) ∧ LoopFrame s.val t.val := by
  obtain ⟨co, hc⟩ := hc
  obtain ⟨bo, hb⟩ := hb
  obtain ⟨t, he, ht, hf⟩ := WordCall.clone 107 106 (by omega) input tape count co bo s hc hb
  have keep (i : ℕ) (hi : i ≠ 106) : t.val.tapes i = s.val.tapes i := by simp [ht, hi]
  exact ⟨t, he, ⟨bo, by simp [ht]⟩, keep,
    hf.2.2.1, hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    (fun i _ _ _ _ hi => keep i hi),
    fun i _ h24 h25 h26 h27 _ _ => hf.2.2.2.2.2.2 i h24 h25 h26 h27⟩

/-- Restore the vector cursor to zero and advance the actual output-row cursor. -/
def rowAdvanceCode : Code := .seq (.call (TapeOps.clear 103)) (BankArray.incrementCode 104)

theorem row_advance (input : List Bool) (tape : ℕ → Bool) (vi ri : List Bool)
    (s : Store) (hvi : BankArray.Word s.val 103 vi) (hri : BankArray.Word s.val 104 ri)
    (hready : Ready s.val (dotValues 0 0)) :
    ∃ cost t, cost ≤ 6*vi.length + 12*ri.length + 22 ∧
      Executes input tape rowAdvanceCode cost s t ∧
      BankArray.Word t.val 103 [] ∧ BankArray.Word t.val 104 (Increment.bits ri) ∧
      Ready t.val (dotValues 0 0) ∧ t.val.memory = s.val.memory ∧
      (∀ i, i ≠ 103 → i ≠ 104 → t.val.tapes i = s.val.tapes i) ∧ MatrixFrame s.val t.val := by
  obtain ⟨vo, hvi⟩ := hvi
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear 103 input tape vi vo s hvi
  have keepA (i : ℕ) (hi : i ≠ 103) : a.val.tapes i = s.val.tapes i := by simp [ha, hi]
  have har := hready.of_tapes (fun i hi => keepA i (by omega))
  obtain ⟨cost, t, hcost, et, hti, _, htm, _, keepT, ft⟩ := BankArray.increment_bank
    104 (by omega) input tape ri a (BankArray.word_of_eq (keepA 104 (by omega)) hri) har.2.1
  have keep (i : ℕ) (hi : i ≠ 103) (hj : i ≠ 104) : t.val.tapes i = s.val.tapes i :=
    (keepT i hj).trans (keepA i hi)
  have ffA : MatrixFrame s.val a.val :=
    ⟨fa.2.1, fa.2.2.2.1, fa.2.2.2.2.1, fun i _ _ _ _ hi _ _ _ => keepA i hi,
      fun i _ _ _ h26 h27 _ _ => fa.2.2.2.2.2.2 i h26 h27⟩
  have ffT : MatrixFrame a.val t.val :=
    ⟨ft.1, ft.2.1, ft.2.2.1, fun i hi _ _ _ _ h104 _ _ => ft.2.2.2.1 i hi h104, ft.2.2.2.2⟩
  refine ⟨6*vi.length+4+cost, t, by omega, ea.seq et, ?_, hti,
    har.of_tapes (fun i hi => keepT i (by omega)), htm.trans fa.2.2.1, keep, ffA.trans ffT⟩
  refine ⟨vo+vi.length, ?_⟩
  rw [keepT 103 (by omega)]
  simp [ha, BitTape.shifted, BitTape.blank]

end Maxwell.Cost.CalibrationMatrix
