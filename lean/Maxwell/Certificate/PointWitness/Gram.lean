import Maxwell.Certificate.PointWitness.Cross
import Maxwell.Certificate.PointWitness.Norm0
import Maxwell.Certificate.PointWitness.Norm1
import Maxwell.Certificate.PointWitness.Inner
import Maxwell.Certificate.Matrix

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee
open scoped ComplexOrder
noncomputable section


def pointGram : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(6427752177035961300787519092163003420250935014042252188057600 : ℝ) / 2^202,
      (480796231951226112797808757686503608862900224 : ℝ) / 2^202;
      (480796231951226112797808757686503608862900224 : ℝ) / 2^202,
      (6427752177035963245345313056087983582074383008508087969513472 : ℝ) / 2^202]

theorem pointGram_binding (i j : Fin 2) :
    inner ℂ (integerVector (![numerator0,numerator1] i) (2^101))
      (integerVector (![numerator0,numerator1] j) (2^101)) = (pointGram i j : ℂ) := by
  have h00 : dotI numerator0 numerator0 = squareNormI numerator0 := rfl
  have h11 : dotI numerator1 numerator1 = squareNormI numerator1 := rfl
  have h10 : dotI numerator1 numerator0 = dotI numerator0 numerator1 := by
    simp only [dotI_eq_sum, mul_comm]
  rw [integerVector_inner]
  fin_cases i <;> fin_cases j <;>
    norm_num [integerVector_inner, pointGram, h00, h11, h10, norm0_checked,
      norm1_checked, cross_checked]

end
end Maxwell.Certificate.PointWitness
