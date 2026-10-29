import Maxwell.Cost.WeightedSource.Split

namespace Maxwell.Cost.WeightedSource.Write
open Structured CalibrationMatrix
open RationalAccumulator (Blank)

private theorem rowFrame_of_write {s t : BitRAMState} (h : BankArray.FrameExcept 37 s t) : RowFrame s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi _ _ h37 => h.2.2.2.1 i hi h37, h.2.2.2.2⟩

private theorem ready_of_write {s t : BitRAMState} {v : ℕ → ℕ} (h : Ready s v)
    (hs : BankArray.Scratch t) (h7 : Blank t 7) (hf : BankArray.FrameExcept 37 s t) : Ready t v :=
  ⟨fun j hj hj' => RationalAccumulator.word_of_eq
    (hf.2.2.2.1 j (Or.inr (by omega)) (by omega)) (h.1 j hj hj'), hs, h7⟩

def code : Code :=
  .seq (BankArray.writeCanonicalCode 514 104 510 515 30)
    (.seq (BankArray.writeCanonicalCode 514 104 511 515 31) clearDotCode)

/-- Two actual indexed writes retain disjoint output arrays, while exact
nested memory semantics allow the caller to preserve any additional data. -/
theorem executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index positiveBase negativeBase clock : List Bool)
    (positiveWords negativeWords : Vector (List Bool) n) (row : Fin n) (positive negative : ℕ)
    (hwidth : 0 < width.length) (hindex : addressValue index = row.val)
    (hclock : clock.length = addressValue width) (hpositive : 0 < addressValue width)
    (hpfit : positive.bits.length ≤ addressValue width) (hnfit : negative.bits.length ≤ addressValue width)
    (hsep : IncidenceEncoding.Separated (addressValue positiveBase) (n * addressValue width)
      (addressValue negativeBase) (n * addressValue width))
    (s : Store) (hready : Ready s.val (dotValues positive negative)) (h37 : Blank s.val 37)
    (h100 : BankArray.Word s.val 514 width) (h104 : BankArray.Word s.val 104 index)
    (h114 : BankArray.Word s.val 510 positiveBase) (h115 : BankArray.Word s.val 511 negativeBase)
    (h101 : BankArray.Word s.val 515 clock)
    (hpa : BitArray.Represents s.val.memory (addressValue positiveBase) (addressValue width) positiveWords)
    (hna : BitArray.Represents s.val.memory (addressValue negativeBase) (addressValue width) negativeWords) :
    ∃ cost t, cost ≤
        BankArray.costCap width index positiveBase (FixedWidth.bits (addressValue width) positive.bits) +
        BankArray.costCap width index negativeBase (FixedWidth.bits (addressValue width) negative.bits) +
        220 * addressValue width + 220 ∧
      Executes input tape code cost s t ∧ Ready t.val (dotValues 0 0) ∧ Blank t.val 37 ∧
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
    BankArray.write_canonical 514 104 510 515 30 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) input tape width index positiveBase clock positiveWords row positive
      hwidth hindex hclock hpositive hpfit s hready.2.1 hready.2.2 h37 h100 h104 h114 h101 hpword hpa
  have hpready := ready_of_write hready hps hp7 hpf
  have hnword : RationalAccumulator.Word p.val 31 negative := by
    simpa [dotValues] using hpready.1 31 (by omega) (by omega)
  have hnarray : BitArray.Represents p.val.memory (addressValue negativeBase) (addressValue width) negativeWords := by
    rw [hpm]
    exact IncidenceEncoding.represents_write_disjoint hna _ _ row _ (FixedWidth.bits_length _ _) hsep.symm
  have metadata (j : ℕ) (hj : 100 ≤ j) {bits : List Bool} (hword : BankArray.Word s.val j bits) :
      BankArray.Word p.val j bits := BankArray.word_of_eq (hpf.2.2.2.1 j (Or.inr (by omega)) (by omega)) hword
  obtain ⟨ncost, q, hncost, en, hnm, hnarray, hns, hn7, hn37, hnf⟩ :=
    BankArray.write_canonical 514 104 511 515 31 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) input tape width index negativeBase clock negativeWords row negative
      hwidth hindex hclock hpositive hnfit p hpready.2.1 hpready.2.2 hp37
      (metadata _ (by omega) h100) (metadata _ (by omega) h104) (metadata _ (by omega) h115)
      (metadata _ (by omega) h101) hnword hnarray
  have hqready := ready_of_write hpready hns hn7 hnf
  have hparray' : BitArray.Represents q.val.memory (addressValue positiveBase) (addressValue width)
      (positiveWords.set row (FixedWidth.bits (addressValue width) positive.bits)) := by
    rw [hnm]
    exact IncidenceEncoding.represents_write_disjoint hparray _ _ row _ (FixedWidth.bits_length _ _) hsep
  obtain ⟨t, et, htready, ht37, htm, htf⟩ := clear_dot input tape positive negative q hqready hn37
  refine ⟨pcost + (ncost + (6*(positive.bits.length+negative.bits.length)+8)), t, by omega,
    ep.seq (en.seq et), htready, ht37, ?_, ?_, ?_,
    ((rowFrame_of_write hpf).trans (rowFrame_of_write hnf)).trans htf⟩
  · rw [htm, hnm, hpm]
  · simpa only [htm] using hparray'
  · simpa only [htm] using hnarray

end Maxwell.Cost.WeightedSource.Write
