import Maxwell.Cost.CalibrationMatrix.Term
import Maxwell.Cost.BankArray.WriteCanonical
import Maxwell.Cost.IncidenceEncoding

/-! The two signed dot-product accumulators are written to their actual
output-array row, then cleared for the next row. -/
namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)

def RowFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i = 4 ∨ 10 ≤ i → i ≠ 30 → i ≠ 31 → i ≠ 37 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem RowFrame.trans {s t u : BitRAMState} (h : RowFrame s t) (k : RowFrame t u) : RowFrame s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    fun i hi h30 h31 h37 => (k.2.2.2.1 i hi h30 h31 h37).trans (h.2.2.2.1 i hi h30 h31 h37),
    fun i hi h24 h25 h26 h27 h28 h29 => (k.2.2.2.2 i hi h24 h25 h26 h27 h28 h29).trans
      (h.2.2.2.2 i hi h24 h25 h26 h27 h28 h29)⟩

private theorem rowFrame_of_write {s t : BitRAMState} (h : BankArray.FrameExcept 37 s t) : RowFrame s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi _ _ h37 => h.2.2.2.1 i hi h37, h.2.2.2.2⟩

private theorem ready_of_write {s t : BitRAMState} {v : ℕ → ℕ} (h : Ready s v)
    (hs : BankArray.Scratch t) (h7 : Blank t 7) (hf : BankArray.FrameExcept 37 s t) : Ready t v :=
  ⟨fun j hj hj' => RationalAccumulator.word_of_eq
    (hf.2.2.2.1 j (Or.inr (by omega)) (by omega)) (h.1 j hj hj'), hs, h7⟩

def clearDotCode : Code := .seq (.call (TapeOps.clear 30)) (.call (TapeOps.clear 31))

theorem clear_dot (input : List Bool) (tape : ℕ → Bool) (positive negative : ℕ)
    (s : Store) (hready : Ready s.val (dotValues positive negative)) (h37 : Blank s.val 37) :
    ∃ t, Executes input tape clearDotCode (6*(positive.bits.length+negative.bits.length)+8) s t ∧
      Ready t.val (dotValues 0 0) ∧ Blank t.val 37 ∧ t.val.memory = s.val.memory ∧ RowFrame s.val t.val := by
  obtain ⟨po, hp⟩ := hready.1 30 (by omega) (by omega)
  obtain ⟨no, hn⟩ := hready.1 31 (by omega) (by omega)
  simp only [dotValues, Function.update_of_ne (show (30:ℕ) ≠ 31 by omega), Function.update_self] at hp hn
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clear 30 input tape positive.bits po s hp
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 31 input tape negative.bits no a (by simpa [ha] using hn)
  have keep (j : ℕ) (h30 : j ≠ 30) (h31 : j ≠ 31) : t.val.tapes j = s.val.tapes j := by
    simp [ht, ha, h30, h31]
  refine ⟨t, ?_, ⟨?_, ?_, ?_⟩, RationalAccumulator.blank_of_eq (keep 37 (by omega) (by omega)) h37,
    ft.2.2.1.trans fa.2.2.1, ?_⟩
  · convert ea.seq et using 1 <;> first | rfl | omega
  · intro j hj hj'
    by_cases h30 : j = 30
    · subst j
      change RationalAccumulator.Word t.val 30 0
      rw [RationalAccumulator.zero_word_iff_blank]
      exact ⟨po + positive.bits.length, by simp [ht, ha]⟩
    · by_cases h31 : j = 31
      · subst j
        change RationalAccumulator.Word t.val 31 0
        rw [RationalAccumulator.zero_word_iff_blank]
        exact ⟨no + negative.bits.length, by simp [ht]⟩
      · have hv : dotValues positive negative j = dotValues 0 0 j := by simp [dotValues, h30, h31]
        rw [← hv]
        exact RationalAccumulator.word_of_eq (keep j h30 h31) (hready.1 j hj hj')
  · rcases hready.2.1 with ⟨h0, h1, h2, h3, h5, h6, h8, h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by omega) (by omega)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by omega) (by omega)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by omega) (by omega)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by omega) (by omega)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by omega) (by omega)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by omega) (by omega)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by omega) (by omega)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by omega) (by omega)) h9⟩
  · exact RationalAccumulator.blank_of_eq (keep 7 (by omega) (by omega)) hready.2.2
  · exact ⟨ft.2.1.trans fa.2.1, ft.2.2.2.1.trans fa.2.2.2.1,
      ft.2.2.2.2.1.trans fa.2.2.2.2.1, fun j _ h30 h31 _ => keep j h30 h31,
      fun j _ _ _ h26 h27 _ _ => (ft.2.2.2.2.2.2 j h26 h27).trans (fa.2.2.2.2.2.2 j h26 h27)⟩

def writeRowCode : Code :=
  .seq (BankArray.writeCanonicalCode 100 104 114 101 30)
    (.seq (BankArray.writeCanonicalCode 100 104 115 101 31) clearDotCode)

/-- Two actual indexed writes retain disjoint output arrays, while exact
nested memory semantics allow the caller to preserve any additional data. -/
theorem write_row {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (width index positiveBase negativeBase clock : List Bool)
    (positiveWords negativeWords : Vector (List Bool) n) (row : Fin n) (positive negative : ℕ)
    (hwidth : 0 < width.length) (hindex : addressValue index = row.val)
    (hclock : clock.length = addressValue width) (hpositive : 0 < addressValue width)
    (hpfit : positive.bits.length ≤ addressValue width) (hnfit : negative.bits.length ≤ addressValue width)
    (hsep : IncidenceEncoding.Separated (addressValue positiveBase) (n * addressValue width)
      (addressValue negativeBase) (n * addressValue width))
    (s : Store) (hready : Ready s.val (dotValues positive negative)) (h37 : Blank s.val 37)
    (h100 : BankArray.Word s.val 100 width) (h104 : BankArray.Word s.val 104 index)
    (h114 : BankArray.Word s.val 114 positiveBase) (h115 : BankArray.Word s.val 115 negativeBase)
    (h101 : BankArray.Word s.val 101 clock)
    (hpa : BitArray.Represents s.val.memory (addressValue positiveBase) (addressValue width) positiveWords)
    (hna : BitArray.Represents s.val.memory (addressValue negativeBase) (addressValue width) negativeWords) :
    ∃ cost t, cost ≤
        BankArray.costCap width index positiveBase (FixedWidth.bits (addressValue width) positive.bits) +
        BankArray.costCap width index negativeBase (FixedWidth.bits (addressValue width) negative.bits) +
        220 * addressValue width + 220 ∧
      Executes input tape writeRowCode cost s t ∧ Ready t.val (dotValues 0 0) ∧ Blank t.val 37 ∧
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
    BankArray.write_canonical 100 104 114 101 30 (by omega) (by omega) (by omega) (by omega) (by omega)
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
    BankArray.write_canonical 100 104 115 101 31 (by omega) (by omega) (by omega) (by omega) (by omega)
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

end Maxwell.Cost.CalibrationMatrix
