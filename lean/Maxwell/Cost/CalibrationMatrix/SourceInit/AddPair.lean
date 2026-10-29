import Maxwell.Cost.CalibrationMatrix.SourceInit.Data
import Maxwell.Cost.DyadicSqrt.Bank

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open Structured RationalAccumulator

set_option maxHeartbeats 800000

def addPairCode (indexBank positiveBank negativeBank : ℕ) : Code :=
  .seq (BankArray.readCanonicalCode 100 indexBank positiveBank 101 32)
    (.seq (BankArray.readCanonicalCode 100 indexBank negativeBank 101 33)
      (.seq (DyadicSqrt.addCode 32 30)
        (.seq (DyadicSqrt.addCode 33 31) clearOperandsCode)))

/-- Read a signed pair from actual indexed arrays and add both channels
to the bank accumulators. No sign normalization or host lookup is used. -/
theorem add_pair {n : ℕ} (indexBank positiveBank negativeBank : ℕ)
    (hiBank : 100 ≤ indexBank) (hpBank : 100 ≤ positiveBank) (hnBank : 100 ≤ negativeBank)
    (input : List Bool) (tape : ℕ → Bool)
    (width index positiveBase negativeBase clock : List Bool)
    (positiveWords negativeWords : Vector (List Bool) n) (row : Fin n)
    (hwidth : 0 < width.length) (hindex : addressValue index = row.val)
    (hclock : clock.length = addressValue width) (B positive negative : ℕ)
    (hwlen : width.length ≤ B) (hW : addressValue width ≤ B) (hilen : index.length ≤ B)
    (hplen : positiveBase.length ≤ B) (hnlen : negativeBase.length ≤ B)
    (hp : positive.bits.length ≤ B) (hn : negative.bits.length ≤ B)
    (s : Store) (hready : Ready s.val (dotValues positive negative))
    (h100 : BankArray.Word s.val 100 width) (hindexBank : BankArray.Word s.val indexBank index)
    (hpositive : BankArray.Word s.val positiveBank positiveBase)
    (hnegative : BankArray.Word s.val negativeBank negativeBase)
    (h101 : BankArray.Word s.val 101 clock)
    (hpa : BitArray.Represents s.val.memory (addressValue positiveBase) (addressValue width) positiveWords)
    (hna : BitArray.Represents s.val.memory (addressValue negativeBase) (addressValue width) negativeWords) :
    ∃ cost t, cost ≤ 50000*(B+2)^2 ∧
      Executes input tape (addPairCode indexBank positiveBank negativeBank) cost s t ∧
      Ready t.val (dotValues (positive+addressValue (positiveWords.get row))
        (negative+addressValue (negativeWords.get row))) ∧ StepFrame s.val t.val := by
  let ap := addressValue (positiveWords.get row)
  let an := addressValue (negativeWords.get row)
  let v1 := Function.update (dotValues positive negative) 32 ap
  let v2 := Function.update v1 33 an
  obtain ⟨c1, a, hc1, e1, r1, f1⟩ := read_operand 100 indexBank positiveBank 101 32
    (by omega) hiBank hpBank (by omega) (by omega) (by omega) input tape
    width index positiveBase clock positiveWords row hwidth hindex hclock s
    (dotValues positive negative) hready (by simp [dotValues]) h100 hindexBank hpositive h101 hpa
  have hana : BitArray.Represents a.val.memory (addressValue negativeBase) (addressValue width)
      negativeWords := by simpa only [f1.1] using hna
  obtain ⟨c2, b, hc2, e2, r2, f2⟩ := read_operand 100 indexBank negativeBank 101 33
    (by omega) hiBank hnBank (by omega) (by omega) (by omega) input tape
    width index negativeBase clock negativeWords row hwidth hindex hclock a v1 r1
    (by simp [v1, dotValues]) (Affine.frame_word f1 _ (by omega) h100)
    (Affine.frame_word f1 _ hiBank hindexBank) (Affine.frame_word f1 _ hnBank hnegative)
    (Affine.frame_word f1 _ (by omega) h101) hana
  obtain ⟨c3, c, hc3, e3, b3, r3, f3⟩ := DyadicSqrt.add 32 30
    (by omega) (by omega) (by omega) (by omega) input tape v2 b r2.1 r2.arithmetic
  let v3 := Function.update v2 30 (ap+positive)
  change Bank c.val v3 at b3
  have hr3 := ready_of_arithmetic r2 b3 r3 f3
  obtain ⟨c4, d, hc4, e4, b4, r4, f4⟩ := DyadicSqrt.add 33 31
    (by omega) (by omega) (by omega) (by omega) input tape v3 c b3 r3
  let v4 := Function.update v3 31 (an+negative)
  change Bank d.val v4 at b4
  have hr4 := ready_of_arithmetic hr3 b4 r4 f4
  obtain ⟨t, e5, b5, r5, f5⟩ := clear_operands input tape v4 d b4 r4
  have hvalues : clearOperands v4 = dotValues (positive+ap) (negative+an) := by
    funext i
    by_cases h30 : i = 30
    · subst i; simp [clearOperands, v4, v3, v2, v1, dotValues, Nat.add_comm]
    by_cases h31 : i = 31
    · subst i; simp [clearOperands, v4, v3, v2, v1, dotValues, Nat.add_comm]
    by_cases h32 : i = 32
    · subst i; simp [clearOperands, v4, v3, v2, v1, dotValues]
    by_cases h33 : i = 33
    · subst i; simp [clearOperands, v4, v3, v2, v1, dotValues]
    by_cases h34 : i = 34
    · subst i; simp [clearOperands, dotValues]
    by_cases h35 : i = 35
    · subst i; simp [clearOperands, dotValues]
    simp [clearOperands, v4, v3, v2, v1, dotValues, h30, h31, h32, h33, h34, h35]
  refine ⟨c1+(c2+(c3+(c4+(6*((v4 32).bits.length+(v4 33).bits.length+
      (v4 34).bits.length+(v4 35).bits.length)+16)))), t, ?_,
    e1.seq (e2.seq (e3.seq (e4.seq e5))), ?_,
    (((f1.trans f2).trans (stepFrame_of_arithmetic f3)).trans (stepFrame_of_arithmetic f4)).trans
      (stepFrame_of_arithmetic f5)⟩
  · have hread1 := hc1.trans (Affine.read_cost_le width index positiveBase clock B
      hwlen hW hilen hplen hclock)
    have hread2 := hc2.trans (Affine.read_cost_le width index negativeBase clock B
      hwlen hW hilen hnlen hclock)
    have hap : ap.bits.length ≤ B :=
      (canonical_length_le _).trans ((hpa.length row).le.trans hW)
    have han : an.bits.length ≤ B :=
      (canonical_length_le _).trans ((hna.length row).le.trans hW)
    change c3 ≤ 230*(ap.bits.length+positive.bits.length+4) at hc3
    change c4 ≤ 230*(an.bits.length+negative.bits.length+4) at hc4
    change c1+(c2+(c3+(c4+(6*(ap.bits.length+an.bits.length+
      (0:ℕ).bits.length+(0:ℕ).bits.length)+16)))) ≤ _
    rw [show (0:ℕ).bits.length = 0 from rfl]
    have hsq : B+2 ≤ (B+2)^2 := Nat.le_self_pow (by decide) _
    clear * - hread1 hread2 hap han hp hn hc3 hc4 hsq
    omega
  · rw [← hvalues]
    exact ready_of_arithmetic hr4 b5 r5 f5

end Maxwell.Cost.CalibrationMatrix.SourceInit
