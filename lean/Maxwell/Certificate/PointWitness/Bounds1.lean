import Maxwell.Certificate.PointWitness.Norm1
import Maxwell.Certificate.PointWitness.Residual1
import Maxwell.Certificate.PointWitness.Vector

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee
noncomputable section

def pointVector1 : EuclideanSpace ℂ Electric := integerVector numerator1 (2^101)
def pointCenter1 : ℝ := (lambdaNumerator1 : ℝ) / 2^80

theorem pointVector1_ne_zero : pointVector1 ≠ 0 := by
  apply integerVector_ne_zero
  · norm_num
  · rw [norm1_checked]
    norm_num

theorem pointResidual1_relative : ‖integerVector residual1 (2^181)‖ ^ 2 ≤
    ((1 : ℝ) / 2^47)^2 * ‖pointVector1‖^2 := by
  rw [pointVector1, integerVector_norm_sq, integerVector_norm_sq,
    norm1_checked, residual1_checked]
  norm_num

theorem pointCenter1_range :
    239 / 25000 < pointCenter1 - 1 / 2^47 ∧
    pointCenter1 + 1 / 2^47 < 957 / 100000 := by
  norm_num [pointCenter1, lambdaNumerator1]

end
end Maxwell.Certificate.PointWitness
