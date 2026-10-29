import Maxwell.Certificate.PointWitness.Bounds1
import Maxwell.Certificate.PointWitness.Action1Complete
import Maxwell.Certificate.PointWitness.Fiber

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee
noncomputable section

theorem pointVector1_residual :
    ‖pointOperator pointVector1 - (pointCenter1 : ℂ) • pointVector1‖^2 ≤
      ((1 : ℝ) / 2^47)^2 * ‖pointVector1‖^2 := by
  have ha := integerVector_point_residual ![1,1,0] numerator1 imageNumerator1
    lambdaNumerator1 (funext numerator1_action)
  have hc : (pointCenter1 : ℂ) = (lambdaNumerator1 : ℂ) / 2^80 := by
    simp only [pointCenter1, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [hc]
  change ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (fiber Maxwell.Spectral.Concrete.material (timeReversalMomentum ![1,1,0]))
      (integerVector numerator1 (2^101)) -
        ((lambdaNumerator1 : ℂ) / 2^80) • integerVector numerator1 (2^101)‖^2 ≤ _
  rw [ha]
  exact pointResidual1_relative

end
end Maxwell.Certificate.PointWitness
