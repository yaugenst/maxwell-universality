import Maxwell.Cost.CalibrationMatrix.Affine.Load
import Maxwell.Cost.CalibrationMatrix.WriteRow

/-! Two indexed output writes retain the signed accumulators so the affine
Horner pass can reuse its already computed scaled source. -/
namespace Maxwell.Cost.CalibrationMatrix.Affine
open Structured
open RationalAccumulator (Blank)

private theorem rowFrame_of_write {s t : BitRAMState} (h : BankArray.FrameExcept 37 s t) : RowFrame s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi _ _ h37 => h.2.2.2.1 i hi h37, h.2.2.2.2⟩

private theorem ready_of_write {s t : BitRAMState} {v : ℕ → ℕ} (h : Ready s v)
    (hs : BankArray.Scratch t) (h7 : Blank t 7) (hf : BankArray.FrameExcept 37 s t) : Ready t v :=
  ⟨fun j hj hj' => RationalAccumulator.word_of_eq
    (hf.2.2.2.1 j (Or.inr (by omega)) (by omega)) (h.1 j hj hj'), hs, h7⟩

def writePairCode (positiveBank negativeBank : ℕ) : Code :=
  .seq (BankArray.writeCanonicalCode 100 104 positiveBank 101 30)
    (BankArray.writeCanonicalCode 100 104 negativeBank 101 31)

theorem write_pair {n : ℕ} (positiveBank negativeBank : ℕ)
    (hpBank : 100 ≤ positiveBank) (hnBank : 100 ≤ negativeBank) (input : List Bool) (tape : ℕ → Bool)
    (width index positiveBase negativeBase clock : List Bool)
    (positiveWords negativeWords : Vector (List Bool) n) (row : Fin n) (positive negative : ℕ)
    (hwidth : 0 < width.length) (hindex : addressValue index = row.val)
    (hclock : clock.length = addressValue width) (hpositive : 0 < addressValue width)
    (hpfit : positive.bits.length ≤ addressValue width) (hnfit : negative.bits.length ≤ addressValue width)
    (hsep : IncidenceEncoding.Separated (addressValue positiveBase) (n * addressValue width)
      (addressValue negativeBase) (n * addressValue width))
    (s : Store) (hready : Ready s.val (dotValues positive negative)) (h37 : Blank s.val 37)
    (h100 : BankArray.Word s.val 100 width) (h104 : BankArray.Word s.val 104 index)
    (hpositiveBank : BankArray.Word s.val positiveBank positiveBase) (hnegativeBank : BankArray.Word s.val negativeBank negativeBase)
    (h101 : BankArray.Word s.val 101 clock)
    (hpa : BitArray.Represents s.val.memory (addressValue positiveBase) (addressValue width) positiveWords)
    (hna : BitArray.Represents s.val.memory (addressValue negativeBase) (addressValue width) negativeWords) :
    ∃ cost t, cost ≤
        BankArray.costCap width index positiveBase (FixedWidth.bits (addressValue width) positive.bits) +
        BankArray.costCap width index negativeBase (FixedWidth.bits (addressValue width) negative.bits) +
        220 * addressValue width + 220 ∧
      Executes input tape (writePairCode positiveBank negativeBank) cost s t ∧ Ready t.val (dotValues positive negative) ∧ Blank t.val 37 ∧
      t.val.memory = MemoryWord.writeBits
        (MemoryWord.writeBits s.val.memory (addressValue positiveBase + row.val * addressValue width)
          (FixedWidth.bits (addressValue width) positive.bits))
        (addressValue negativeBase + row.val * addressValue width) (FixedWidth.bits (addressValue width) negative.bits) ∧
      BitArray.Represents t.val.memory (addressValue positiveBase) (addressValue width)
        (positiveWords.set row (FixedWidth.bits (addressValue width) positive.bits)) ∧
      BitArray.Represents t.val.memory (addressValue negativeBase) (addressValue width)
        (negativeWords.set row (FixedWidth.bits (addressValue width) negative.bits)) ∧ RowFrame s.val t.val := by
  have hpword : RationalAccumulator.Word s.val 30 positive := by simpa [dotValues] using hready.1 30 (by omega) (by omega)
  obtain ⟨pcost, p, hpcost, ep, hpm, hparray, hps, hp7, hp37, hpf⟩ :=
    BankArray.write_canonical 100 104 positiveBank 101 30 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) input tape width index positiveBase clock positiveWords row positive
      hwidth hindex hclock hpositive hpfit s hready.2.1 hready.2.2 h37 h100 h104 hpositiveBank h101 hpword hpa
  have hpready := ready_of_write hready hps hp7 hpf
  have hnword : RationalAccumulator.Word p.val 31 negative := by
    simpa [dotValues] using hpready.1 31 (by omega) (by omega)
  have hnarray : BitArray.Represents p.val.memory (addressValue negativeBase) (addressValue width) negativeWords := by
    rw [hpm]
    exact IncidenceEncoding.represents_write_disjoint hna _ _ row _ (FixedWidth.bits_length _ _) hsep.symm
  have metadata (j : ℕ) (hj : 100 ≤ j) {bits : List Bool} (hword : BankArray.Word s.val j bits) :
      BankArray.Word p.val j bits := BankArray.word_of_eq (hpf.2.2.2.1 j (Or.inr (by omega)) (by omega)) hword
  obtain ⟨ncost, q, hncost, en, hnm, hnarray, hns, hn7, hn37, hnf⟩ :=
    BankArray.write_canonical 100 104 negativeBank 101 31 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) input tape width index negativeBase clock negativeWords row negative
      hwidth hindex hclock hpositive hnfit p hpready.2.1 hpready.2.2 hp37
      (metadata _ (by omega) h100) (metadata _ (by omega) h104) (metadata _ (by omega) hnegativeBank)
      (metadata _ (by omega) h101) hnword hnarray
  have hqready := ready_of_write hpready hns hn7 hnf
  have hparray' : BitArray.Represents q.val.memory (addressValue positiveBase) (addressValue width)
      (positiveWords.set row (FixedWidth.bits (addressValue width) positive.bits)) := by
    rw [hnm]
    exact IncidenceEncoding.represents_write_disjoint hparray _ _ row _ (FixedWidth.bits_length _ _) hsep
  refine ⟨pcost+ncost, q, by omega, ep.seq en, hqready, hn37, ?_, hparray', hnarray,
    (rowFrame_of_write hpf).trans (rowFrame_of_write hnf)⟩
  rw [hnm, hpm]

end Maxwell.Cost.CalibrationMatrix.Affine
