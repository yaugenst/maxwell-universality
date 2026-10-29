import Maxwell.Cost.CalibrationMatrix.Iteration
import Maxwell.Cost.NormalizeCoefficient.Load

/-! Actual indexed signed-vector loading and scalar accumulation for the
Horner affine pass. Persistent scalar words survive each use. -/
namespace Maxwell.Cost.CalibrationMatrix.Affine
open Structured
open RationalAccumulator (Bank Blank)

set_option maxHeartbeats 800000

theorem frame_word {s t : BitRAMState} (h : StepFrame s t) (i : ℕ) (hi : 100 ≤ i)
    {bits : List Bool} (hw : BankArray.Word s i bits) : BankArray.Word t i bits :=
  BankArray.word_of_eq (h.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega))) hw

theorem frame_number {s t : BitRAMState} (h : StepFrame s t) (i : ℕ) (hi : 100 ≤ i)
    {n : ℕ} (hw : RationalAccumulator.Word s i n) : RationalAccumulator.Word t i n :=
  RationalAccumulator.word_of_eq (h.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega))) hw

def loadCode (positiveBank negativeBank scalarBank : ℕ) : Code :=
  .seq (BankArray.readCanonicalCode 100 104 positiveBank 101 32)
    (.seq (BankArray.readCanonicalCode 100 104 negativeBank 101 33)
      (.call (WordTransfer.clone scalarBank 34)))

theorem load {n : ℕ} (positiveBank negativeBank scalarBank : ℕ)
    (hpBank : 100 ≤ positiveBank) (hnBank : 100 ≤ negativeBank) (hsBank : 100 ≤ scalarBank)
    (input : List Bool) (tape : ℕ → Bool)
    (width index positiveBase negativeBase clock : List Bool)
    (positiveWords negativeWords : Vector (List Bool) n) (row : Fin n)
    (hwidth : 0 < width.length) (hindex : addressValue index = row.val)
    (hclock : clock.length = addressValue width)
    (positive negative scalar : ℕ) (s : Store)
    (hready : Ready s.val (dotValues positive negative))
    (h100 : BankArray.Word s.val 100 width) (h104 : BankArray.Word s.val 104 index)
    (hpositive : BankArray.Word s.val positiveBank positiveBase)
    (hnegative : BankArray.Word s.val negativeBank negativeBase)
    (h101 : BankArray.Word s.val 101 clock)
    (hscalar : RationalAccumulator.Word s.val scalarBank scalar)
    (hpa : BitArray.Represents s.val.memory (addressValue positiveBase) (addressValue width) positiveWords)
    (hna : BitArray.Represents s.val.memory (addressValue negativeBase) (addressValue width) negativeWords) :
    ∃ cost t, cost ≤ BankArray.costCap width index positiveBase clock +
      BankArray.costCap width index negativeBase clock + 64*addressValue width +
      15*scalar.bits.length + 87 ∧
      Executes input tape (loadCode positiveBank negativeBank scalarBank) cost s t ∧
      Ready t.val (termValues positive negative (addressValue (positiveWords.get row))
        (addressValue (negativeWords.get row)) scalar 0) ∧ StepFrame s.val t.val := by
  let v1 := Function.update (dotValues positive negative) 32 (addressValue (positiveWords.get row))
  let v2 := Function.update v1 33 (addressValue (negativeWords.get row))
  obtain ⟨c1, a, hc1, ea, har, haf⟩ := read_operand 100 104 positiveBank 101 32
    (by omega) (by omega) hpBank (by omega) (by omega) (by omega) input tape
    width index positiveBase clock positiveWords row hwidth hindex hclock s
    (dotValues positive negative) hready (by simp [dotValues]) h100 h104 hpositive h101 hpa
  have hana : BitArray.Represents a.val.memory (addressValue negativeBase) (addressValue width) negativeWords := by
    simpa only [haf.1] using hna
  obtain ⟨c2, b, hc2, eb, hbr, hbf⟩ := read_operand 100 104 negativeBank 101 33
    (by omega) (by omega) hnBank (by omega) (by omega) (by omega) input tape
    width index negativeBase clock negativeWords row hwidth hindex hclock a v1 har
    (by simp [v1, dotValues]) (frame_word haf _ (by omega) h100)
    (frame_word haf _ (by omega) h104) (frame_word haf _ hnBank hnegative)
    (frame_word haf _ (by omega) h101) hana
  have hbs := frame_number (haf.trans hbf) scalarBank hsBank hscalar
  obtain ⟨t, et, htb, htr, htf⟩ := NormalizeCoefficient.clone_external scalarBank 34
    (by omega) (by omega) (by omega) input tape v2 scalar b hbr.1 hbr.arithmetic
    (by simp [v2, v1, dotValues]) hbs
  have hvalues : Function.update v2 34 scalar = termValues positive negative
      (addressValue (positiveWords.get row)) (addressValue (negativeWords.get row)) scalar 0 := by
    funext i
    by_cases h35 : i = 35
    · subst i; simp [v2, v1, termValues, dotValues]
    · simp [v2, v1, termValues, h35]
  refine ⟨c1+(c2+(15*scalar.bits.length+17)), t, by omega,
    ea.seq (eb.seq et), ?_, (haf.trans hbf).trans (stepFrame_of_arithmetic htf)⟩
  rw [← hvalues]
  exact ready_of_arithmetic hbr htb htr htf

def scaledTermCode (positiveBank negativeBank scalarBank : ℕ) : Code :=
  .seq (loadCode positiveBank negativeBank scalarBank) termCode

theorem read_cost_le (width index base clock : List Bool) (B : ℕ)
    (hwidth : width.length ≤ B) (hvalue : addressValue width ≤ B)
    (hindex : index.length ≤ B) (hbase : base.length ≤ B)
    (hclock : clock.length = addressValue width) :
    BankArray.costCap width index base clock + 32*addressValue width+35 ≤ 20000*(B+2)^2 := by
  calc
    _ ≤ 1000*(B+B+B+5)^2 + B*(15*(B+B+B+1+B)+24) + 4 +
        40*(B+B+B+B+B+3) + 32*B+35 := by
      dsimp [BankArray.costCap, ArrayAccess.costCap]
      rw [hclock]
      gcongr
    _ ≤ _ := by nlinarith

theorem scaled_term {n : ℕ} (positiveBank negativeBank scalarBank : ℕ)
    (hpBank : 100 ≤ positiveBank) (hnBank : 100 ≤ negativeBank) (hsBank : 100 ≤ scalarBank)
    (input : List Bool) (tape : ℕ → Bool)
    (width index positiveBase negativeBase clock : List Bool)
    (positiveWords negativeWords : Vector (List Bool) n) (row : Fin n)
    (hwidth : 0 < width.length) (hindex : addressValue index = row.val)
    (hclock : clock.length = addressValue width)
    (positive negative scalar B : ℕ) (hwidthB : width.length ≤ B) (hvalueB : addressValue width ≤ B)
    (hindexB : index.length ≤ B) (hpbaseB : positiveBase.length ≤ B) (hnbaseB : negativeBase.length ≤ B)
    (hpB : positive.bits.length ≤ B) (hnB : negative.bits.length ≤ B) (hsB : scalar.bits.length ≤ B)
    (s : Store) (hready : Ready s.val (dotValues positive negative))
    (h100 : BankArray.Word s.val 100 width) (h104 : BankArray.Word s.val 104 index)
    (hpositive : BankArray.Word s.val positiveBank positiveBase)
    (hnegative : BankArray.Word s.val negativeBank negativeBase)
    (h101 : BankArray.Word s.val 101 clock)
    (hscalar : RationalAccumulator.Word s.val scalarBank scalar)
    (hpa : BitArray.Represents s.val.memory (addressValue positiveBase) (addressValue width) positiveWords)
    (hna : BitArray.Represents s.val.memory (addressValue negativeBase) (addressValue width) negativeWords) :
    ∃ cost t, cost ≤ 500000*(B+2)^2 ∧
      Executes input tape (scaledTermCode positiveBank negativeBank scalarBank) cost s t ∧
      Ready t.val (dotValues (positive+addressValue (positiveWords.get row)*scalar)
        (negative+addressValue (negativeWords.get row)*scalar)) ∧ StepFrame s.val t.val := by
  obtain ⟨c1, a, hc1, ea, har, haf⟩ := load positiveBank negativeBank scalarBank hpBank hnBank hsBank
    input tape width index positiveBase negativeBase clock positiveWords negativeWords row
    hwidth hindex hclock positive negative scalar s hready h100 h104 hpositive hnegative h101 hscalar hpa hna
  have hap := (canonical_length_le (positiveWords.get row)).trans ((hpa.length row).le.trans hvalueB)
  have han := (canonical_length_le (negativeWords.get row)).trans ((hna.length row).le.trans hvalueB)
  have hbits : ∀ i, 30 ≤ i → i ≤ 35 →
      (termValues positive negative (addressValue (positiveWords.get row))
        (addressValue (negativeWords.get row)) scalar 0 i).bits.length ≤ B := by
    intro i hi hi'
    interval_cases i <;> simp_all [termValues, dotValues]
  obtain ⟨c2, t, hc2, et, htr, htf⟩ := term input tape positive negative
    (addressValue (positiveWords.get row)) (addressValue (negativeWords.get row)) scalar 0 B hbits a har
  refine ⟨c1+c2, t, ?_, ea.seq et, ?_, haf.trans htf⟩
  · have hp := read_cost_le width index positiveBase clock B hwidthB hvalueB hindexB hpbaseB hclock
    have hn := read_cost_le width index negativeBase clock B hwidthB hvalueB hindexB hnbaseB hclock
    nlinarith
  · simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] using htr

end Maxwell.Cost.CalibrationMatrix.Affine
