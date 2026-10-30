import Maxwell.Continuum.CalibrationPowerNormalize
import Maxwell.Continuum.CalibrationInterval

/-! Certified Rayleigh evaluation and rational output enclosures.
All errors refer to the actual bounded operator and actual eigenpair. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open TopEigenPerturbation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rayleigh_complex_error (A : H →L[ℂ] H) {u v : H} {mu M : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : A u = (mu : ℂ) • u) (hA : ‖A‖ ≤ M) :
    ‖inner ℂ v (A v)-(mu : ℂ)‖ ≤ 2*M*‖v-u‖ := by
  have hunit : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K,hu]; simp
  have heq : inner ℂ v (A v)-(mu : ℂ) =
      inner ℂ (v-u) (A v)+inner ℂ u (A (v-u)) := by
    rw [map_sub,inner_sub_left,inner_sub_right,he,inner_smul_right,hunit,mul_one]
    ring
  rw [heq]
  have hav : ‖A v‖ ≤ M := by simpa only [hv,mul_one] using A.le_of_opNorm_le hA v
  have had := A.le_of_opNorm_le hA (v-u)
  calc
    _ ≤ ‖inner ℂ (v-u) (A v)‖+‖inner ℂ u (A (v-u))‖ := norm_add_le _ _
    _ ≤ ‖v-u‖*‖A v‖+‖u‖*‖A (v-u)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖v-u‖*M+1*(M*‖v-u‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hav (norm_nonneg _))
        (by rw [hu,one_mul,one_mul]; exact had)
    _ = _ := by ring

theorem rayleigh_evaluation_error (A : H →L[ℂ] H) {u v w : H} {mu M ε : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : A u = (mu : ℂ) • u) (hA : ‖A‖ ≤ M)
    (hw : ‖w-A v‖ ≤ ε) : |(inner ℂ v w).re-mu| ≤ 2*M*‖v-u‖+ε := by
  have hi : ‖inner ℂ v w-inner ℂ v (A v)‖ ≤ ε := by
    rw [← inner_sub_right]
    exact (norm_inner_le_norm _ _).trans (by rw [hv,one_mul]; exact hw)
  have heq : inner ℂ v w-(mu : ℂ) =
    (inner ℂ v (A v)-(mu : ℂ))+(inner ℂ v w-inner ℂ v (A v)) := by ring
  have hb : ‖inner ℂ v w-(mu : ℂ)‖ ≤ 2*M*‖v-u‖+ε := by
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (rayleigh_complex_error A hu hv he hA) hi)
  have hr := Complex.abs_re_le_norm (inner ℂ v w-(mu : ℂ))
  simpa only [Complex.sub_re,Complex.ofReal_re] using hr.trans hb

namespace RationalInterval

/-- Rational enclosure obtained by dividing a rational Rayleigh value
and its proved absolute error by a positive rational scale. -/
def fromScaledError (q ε s : ℚ) (hε : 0 ≤ ε) (hs : 0 < s) : RationalInterval where
  lo := (q-ε)/s
  hi := (q+ε)/s
  ordered := div_le_div_of_nonneg_right (by linarith) hs.le

theorem fromScaledError_contains (q ε s : ℚ) (hε : 0 ≤ ε) (hs : 0 < s)
    {x : ℝ} (hx : |(q : ℝ)-(s : ℝ)*x| ≤ (ε : ℝ)) :
    (fromScaledError q ε s hε hs).Contains x := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  obtain ⟨hl,hu⟩ := abs_le.mp hx
  constructor
  · change (((q-ε)/s : ℚ) : ℝ) ≤ x
    push_cast
    exact (div_le_iff₀ hsR).mpr (by nlinarith)
  · change x ≤ (((q+ε)/s : ℚ) : ℝ)
    push_cast
    exact (le_div_iff₀ hsR).mpr (by nlinarith)

theorem fromScaledError_width (q ε s : ℚ) (hε : 0 ≤ ε) (hs : 0 < s) :
    (fromScaledError q ε s hε hs).width = 2*ε/s := by
  unfold Maxwell.Certificate.Interval.width fromScaledError
  ring

theorem fromScaledError_midpoint (q ε s : ℚ) (hε : 0 ≤ ε) (hs : 0 < s) :
    (fromScaledError q ε s hε hs).midpoint = q/s := by
  unfold Maxwell.Certificate.Interval.midpoint fromScaledError
  ring

end RationalInterval

#print axioms rayleigh_evaluation_error
#print axioms RationalInterval.fromScaledError_contains

end Maxwell.Continuum.Calibration
