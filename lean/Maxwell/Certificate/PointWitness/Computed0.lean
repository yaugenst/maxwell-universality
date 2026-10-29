import Maxwell.Certificate.PointWitness.Bounds0
import Maxwell.Certificate.PointWitness.Action0Complete
import Maxwell.Certificate.PointWitness.Fiber

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee
noncomputable section

theorem pointVector0_residual :
    ‖pointOperator pointVector0 - (pointCenter0 : ℂ) • pointVector0‖^2 ≤
      ((1 : ℝ) / 2^47)^2 * ‖pointVector0‖^2 := by
  have ha := integerVector_point_residual ![1,1,0] numerator0 imageNumerator0
    lambdaNumerator0 (funext numerator0_action)
  have hc : (pointCenter0 : ℂ) = (lambdaNumerator0 : ℂ) / 2^80 := by
    simp only [pointCenter0, Complex.ofReal_div, Complex.ofReal_intCast,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [hc]
  change ‖Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (fiber Maxwell.Spectral.Concrete.material (timeReversalMomentum ![1,1,0]))
      (integerVector numerator0 (2^101)) -
        ((lambdaNumerator0 : ℂ) / 2^80) • integerVector numerator0 (2^101)‖^2 ≤ _
  rw [ha]
  exact pointResidual0_relative

end
end Maxwell.Certificate.PointWitness
