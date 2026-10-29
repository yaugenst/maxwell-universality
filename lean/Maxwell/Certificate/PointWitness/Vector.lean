import Maxwell.Certificate.PointWitness.NormDefs
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace Maxwell.Certificate.PointWitness
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Certificate.PrimitiveBinding
open scoped Matrix
noncomputable section

def integerVector (v : Electric → ℤ) (d : ℝ) : EuclideanSpace ℂ Electric :=
  WithLp.toLp 2 (fun e => (v e : ℂ) / (d : ℂ))

@[simp] theorem integerVector_apply (v : Electric → ℤ) (d : ℝ) (e : Electric) :
    integerVector v d e = (v e : ℂ) / (d : ℂ) := rfl

theorem integerVector_norm_sq (v : Electric → ℤ) (d : ℝ) :
    ‖integerVector v d‖ ^ 2 = (squareNormI v : ℝ) / d ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, squareNormI_eq_sum]
  simp only [integerVector_apply, norm_div, Complex.norm_intCast, Complex.norm_real,
    Real.norm_eq_abs, div_pow, sq_abs, Int.cast_sum, Int.cast_mul]
  simp only [Finset.sum_div, pow_two]

theorem integerVector_ne_zero (v : Electric → ℤ) (d : ℝ)
    (hd : d ≠ 0) (hv : 0 < squareNormI v) : integerVector v d ≠ 0 := by
  intro h
  have hs := integerVector_norm_sq v d
  have hv' : (0 : ℝ) < (squareNormI v : ℝ) := by exact_mod_cast hv
  rw [h, norm_zero, zero_pow (by decide)] at hs
  have := div_pos hv' (sq_pos_of_ne_zero hd)
  linarith

/-- The verified sparse integer action yields the genuine complex Bloch
matrix action after scaling the vector denominator. -/
theorem integerVector_action (k : Translation) (v : Electric → ℤ) (d : ℚ) (hd : d ≠ 0) :
    Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (PrimitiveYee.fiber Concrete.material (timeReversalMomentum k))
      (integerVector v (d : ℝ)) =
    integerVector (fiberActionI k v) (536870912 * (d : ℝ)) := by
  ext e
  change (PrimitiveYee.fiber Concrete.material (timeReversalMomentum k) *ᵥ
      (fun e => (v e : ℂ) / ((d : ℝ) : ℂ))) e = _
  rw [← fiber_binding]
  have hmap := RingHom.map_mulVec (Rat.castHom ℂ) (fiberQ k)
    (fun e => (v e : ℚ) / d) e
  have he := fiberActionI_cast k v d hd e
  rw [← fiberActionQ_correct] at he
  have he' := congrArg (Rat.castHom ℂ) he
  rw [hmap] at he'
  simpa only [Function.comp_def, Rat.coe_castHom, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Complex.ofReal_mul, Complex.ofReal_ratCast,
    Complex.ofReal_ofNat, integerVector_apply] using he'

/-- Exact residual scaling for the frozen 100-bit projected point witnesses. -/
theorem integerVector_point_residual (k : Translation) (v w : Electric → ℤ)
    (p : ℤ) (ha : fiberActionI k v = w) :
    Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (PrimitiveYee.fiber Concrete.material (timeReversalMomentum k))
      (integerVector v (2^101)) - ((p : ℂ) / 2^80) • integerVector v (2^101) =
      integerVector (fun e => w e * 2^51 - p * v e) (2^181) := by
  have h := integerVector_action k v (2^101) (by norm_num)
  simp only [Rat.cast_pow, Rat.cast_ofNat] at h
  rw [h, ha]
  ext e
  simp only [PiLp.sub_apply, PiLp.smul_apply, integerVector_apply, smul_eq_mul,
    Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  norm_num
  ring

end
end Maxwell.Certificate.PointWitness
