import Maxwell.Cost.CalibrationSource.RepackData
import Maxwell.Cost.CalibrationMatrix.Product
import Maxwell.Cost.Structured.Footprint

namespace Maxwell.Cost.CalibrationSource.Factor
open Structured CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 1600000

/-- The fixed factor is physically emitted, used for both signed channels,
and cleared. Its value is part of the finite program, not an input product. -/
def multiplyCode (factor : ℕ) : Code := .seq (BinaryPrecision.literalCode 1 factor)
  (.seq (productCode 30) (.seq (productCode 31) (.call (TapeOps.clear 1))))

private theorem product_tapes {input : List Bool} {tape : ℕ → Bool} {s t : Store}
    {cost target : ℕ} (ht : target = 30 ∨ target = 31)
    (he : Executes input tape (productCode target) cost s t)
    (hf : RationalAccumulator.Frame s.val t.val) (j : ℕ) (hj : 4 ≤ j)
    (h30 : j ≠ 30) (h31 : j ≠ 31) : t.val.tapes j = s.val.tapes j := by
  by_cases h : j < 30 ∨ 36 < j
  · exact hf.2.2.2.2.2.1 j hj h
  · have hj' : 32 ≤ j ∧ j ≤ 36 := by omega
    rcases hj' with ⟨hlo,hhi⟩
    rcases ht with rfl | rfl <;> interval_cases j <;>
      exact he.protectsTape _ (by decide)

/-- Exact multiplication of the two loaded channels, including zero factors
and zero coefficients, with every persistent metadata tape preserved. -/
theorem multiply (factor positive negative B : ℕ)
    (hf : factor.bits.length ≤ B) (hp : positive.bits.length ≤ B)
    (hn : negative.bits.length ≤ B) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (hr : Ready s.val (dotValues positive negative)) :
    ∃ cost t, cost ≤ 10000*(B+2)^2 ∧ Executes input tape (multiplyCode factor) cost s t ∧
      Ready t.val (dotValues (factor*positive) (factor*negative)) ∧
      t.val.memory = s.val.memory ∧ Repack.Frame s.val t.val := by
  obtain ⟨a,ea,aw,fa⟩ := BinaryPrecision.literal 1 factor input tape s hr.2.1.2.1
  have ab : RationalAccumulator.Bank a.val (dotValues positive negative) := by
    intro j hj hj'
    exact RationalAccumulator.word_of_eq (fa.tapes j (by simp;omega)) (hr.1 j hj hj')
  have ar : RationalAccumulator.Scratch a.val factor :=
    ⟨RationalAccumulator.blank_of_eq (fa.tapes 0 (by decide)) hr.2.1.1,aw,
      RationalAccumulator.blank_of_eq (fa.tapes 2 (by decide)) hr.2.1.2.2.1,
      RationalAccumulator.blank_of_eq (fa.tapes 3 (by decide)) hr.2.1.2.2.2.1⟩
  obtain ⟨pc,b,hpc,ep,bb,br,fb⟩ := product 30 (by decide) (by decide)
    input tape (dotValues positive negative) factor a ab ar
  have bb' : RationalAccumulator.Bank b.val (dotValues (factor*positive) negative) := by
    convert bb using 1
    funext j
    by_cases h30 : j = 30 <;> by_cases h31 : j = 31 <;> simp_all [dotValues]
  obtain ⟨nc,c,hnc,en,cb,cr,fc⟩ := product 31 (by decide) (by decide)
    input tape (dotValues (factor*positive) negative) factor b bb' br
  have cb' : RationalAccumulator.Bank c.val (dotValues (factor*positive) (factor*negative)) := by
    convert cb using 1
    funext j
    by_cases h30 : j = 30 <;> by_cases h31 : j = 31 <;> simp_all [dotValues]
  obtain ⟨t,et,tb,tr,ft⟩ := RationalAccumulator.clear_one input tape
    (dotValues (factor*positive) (factor*negative)) factor c cb' cr
  have clearSame (j : ℕ) (hj : j ≠ 1) : t.val.tapes j = c.val.tapes j := by
    apply et.protectsTape j
    simp [Code.protectsTape,BitRAM.protectsTape,TapeOps.clear,
      BitRAMInstruction.protectsTape,hj,ne_comm]
  have keep (j : ℕ) (hj : 4 ≤ j) (h30 : j ≠ 30) (h31 : j ≠ 31) :
      t.val.tapes j = s.val.tapes j :=
    (clearSame j (by omega)).trans ((product_tapes (Or.inr rfl) en fc j hj h30 h31).trans
      ((product_tapes (Or.inl rfl) ep fb j hj h30 h31).trans (fa.tapes j (by simp;omega))))
  refine ⟨10*factor.bits.length+7+(pc+(nc+(6*factor.bits.length+4))),t,?_,
    ea.seq (ep.seq (en.seq et)),⟨tb,?_,RationalAccumulator.blank_of_eq (keep 7 (by omega) (by omega) (by omega)) hr.2.2⟩,
    ft.2.2.1.trans (fc.2.2.1.trans (fb.2.2.1.trans fa.memory)),
    ⟨ft.2.1.trans (fc.2.1.trans (fb.2.1.trans fa.inputHead)),
      ft.2.2.2.1.trans (fc.2.2.2.1.trans (fb.2.2.2.1.trans fa.randomCursor)),
      ft.2.2.2.2.1.trans (fc.2.2.2.2.1.trans (fb.2.2.2.2.1.trans fa.output)),
      fun j hj h30 h31 _ _ => keep j (by omega) h30 h31⟩⟩
  · simp only [dotValues] at hpc hnc
    have hp' := hpc.trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (show
      factor.bits.length+positive.bits.length+3 ≤ 2*B+3 by omega) 2))
    have hn' := hnc.trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (show
      factor.bits.length+negative.bits.length+3 ≤ 2*B+3 by omega) 2))
    nlinarith
  · exact ⟨tr.1,(RationalAccumulator.zero_word_iff_blank _ _).mp tr.2.1,tr.2.2.1,tr.2.2.2,
      RationalAccumulator.blank_of_eq (keep 5 (by omega) (by omega) (by omega)) hr.2.1.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by omega) (by omega) (by omega)) hr.2.1.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by omega) (by omega) (by omega)) hr.2.1.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by omega) (by omega) (by omega)) hr.2.1.2.2.2.2.2.2.2⟩

end Maxwell.Cost.CalibrationSource.Factor
