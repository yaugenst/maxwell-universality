import Maxwell.Certificate.PointWitness.Norm0
import Maxwell.Certificate.PointWitness.Residual0
import Maxwell.Certificate.PointWitness.Vector

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee
noncomputable section

def pointVector0 : EuclideanSpace ℂ Electric := integerVector numerator0 (2^101)
def pointCenter0 : ℝ := (lambdaNumerator0 : ℝ) / 2^80

theorem pointVector0_ne_zero : pointVector0 ≠ 0 := by
  apply integerVector_ne_zero
  · norm_num
  · rw [norm0_checked]
    norm_num

theorem pointResidual0_relative : ‖integerVector residual0 (2^181)‖ ^ 2 ≤
    ((1 : ℝ) / 2^47)^2 * ‖pointVector0‖^2 := by
  rw [pointVector0, integerVector_norm_sq, integerVector_norm_sq,
    norm0_checked, residual0_checked]
  norm_num

theorem pointCenter0_range :
    239 / 25000 < pointCenter0 - 1 / 2^47 ∧
    pointCenter0 + 1 / 2^47 < 957 / 100000 := by
  norm_num [pointCenter0, lambdaNumerator0]

end
end Maxwell.Certificate.PointWitness
