import Maxwell.Certificate.PointWitness.Vector
import Maxwell.Certificate.PointWitness.DotDefs
namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PrimitiveYee
noncomputable section

theorem integerVector_inner (v w : Electric → ℤ) (d e : ℝ) :
    inner ℂ (integerVector v d) (integerVector w e) =
      ((dotI v w : ℝ) / (d * e) : ℂ) := by
  simp only [PiLp.inner_apply, integerVector_apply]
  have h (i : Electric) : inner ℂ ((v i : ℂ) / (d : ℂ)) ((w i : ℂ) / (e : ℂ)) =
      ((v i : ℝ) * (w i : ℝ) / (d * e) : ℂ) := by
    simp [RCLike.inner_apply, div_mul_div_comm, mul_comm]
  simp_rw [h]
  simp only [dotI_eq_sum, Int.cast_sum, Int.cast_mul,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_intCast, Finset.sum_div]

end
end Maxwell.Certificate.PointWitness
