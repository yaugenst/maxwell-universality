import Maxwell.Certificate.DerivativeAction
import Maxwell.Certificate.PointWitness.Vector

namespace Maxwell.Certificate.DerivativeBinding
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Certificate.PrimitiveBinding Maxwell.Certificate.PointWitness
open Maxwell.Spectral.PeriodicYee (Direction)
open Matrix
noncomputable section

def BOperator (k : Translation) (i : Direction) :
    EuclideanSpace ℂ Electric →L[ℂ] EuclideanSpace ℂ Electric :=
  Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (castQ (BQ k i))

theorem integerVector_B_action (k : Translation) (i : Direction)
    (v : Electric → ℤ) (d : ℚ) :
    BOperator k i (integerVector v (d : ℝ)) =
      integerVector (BActionI k i v) (d : ℝ) := by
  ext e
  change ((BQ k i).map ((↑) : ℚ → ℂ) *ᵥ
    (fun e => (v e : ℂ) / ((d : ℝ) : ℂ))) e = _
  have hmap := RingHom.map_mulVec (Rat.castHom ℂ) (BQ k i)
    (fun e => (v e : ℚ) / d) e
  have he := congrArg (Rat.castHom ℂ) (BActionI_cast k i v d e)
  rw [hmap] at he
  simpa only [Function.comp_def, Rat.coe_castHom, Rat.cast_div, Rat.cast_intCast,
    Complex.ofReal_ratCast, integerVector_apply] using he

/-- The saved six-column solve residual is the residual of the genuine fiber
and its genuine first derivative matrix. -/
theorem integerVector_corrector_residual (k : Translation) (i : Direction)
    (v y w b : Electric → ℤ) (p : ℤ)
    (hy : fiberActionI k y = w) (hb : BActionI k i v = b) :
    Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (PrimitiveYee.fiber Concrete.material (timeReversalMomentum k))
      (integerVector y (2^101)) - ((p : ℂ) / 2^80) • integerVector y (2^101) -
      BOperator k i (integerVector v (2^101)) =
      integerVector (fun e => w e * 2^51 - p * y e - b e * 2^80) (2^181) := by
  rw [integerVector_point_residual k y w p hy]
  have h := integerVector_B_action k i v (2^101)
  simp only [Rat.cast_pow, Rat.cast_ofNat] at h
  rw [h, hb]
  ext e
  simp only [PiLp.sub_apply, integerVector_apply, Int.cast_sub, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, Complex.ofReal_pow, Complex.ofReal_ofNat]
  norm_num
  ring

end
end Maxwell.Certificate.DerivativeBinding
