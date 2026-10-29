import Maxwell.Continuum.FiberNormalizationBilinear
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-! A fixed analytic square-root branch normalizes the actual bilinear
pairing near a real unit vector, with a uniform multiplier bound. -/

noncomputable section
namespace Maxwell.Continuum.FiberNormalization

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

theorem sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z :=
  Complex.cpow_nat_inv_pow z (by decide : (2 : ℕ) ≠ 0)

theorem sqrt_norm_sq (z : ℂ) : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
  simpa only [norm_pow] using congrArg norm (sqrt_sq z)

theorem near_one_re_pos (z : ℂ) (hz : ‖z - 1‖ ≤ 11 / 25) : 0 < z.re := by
  have h := (Complex.abs_re_le_norm (z - 1)).trans hz
  rw [Complex.sub_re, Complex.one_re] at h
  have hh := (abs_le.mp h).1
  linarith

theorem near_one_ne_zero (z : ℂ) (hz : ‖z - 1‖ ≤ 11 / 25) : z ≠ 0 := by
  have h := near_one_re_pos z hz
  intro h0
  simp only [h0, Complex.zero_re, lt_self_iff_false] at h

theorem sqrt_ne_zero (z : ℂ) (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  intro h
  have hs := sqrt_sq z
  rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
  exact hz hs.symm

theorem inv_sqrt_norm_le (z : ℂ) (hz : ‖z - 1‖ ≤ 11 / 25) : ‖(Complex.sqrt z)⁻¹‖ ≤ 3 / 2 := by
  have ht := norm_sub_le z (z - 1)
  rw [sub_sub_cancel, norm_one] at ht
  have hs := sqrt_norm_sq z
  have hn := norm_nonneg (Complex.sqrt z)
  have hp := norm_pos_iff.mpr (sqrt_ne_zero z (near_one_ne_zero z hz))
  rw [norm_inv, ← one_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem analyticAt_sqrt (z : ℂ) (hz : ‖z - 1‖ ≤ 11 / 25) : AnalyticAt ℂ Complex.sqrt z :=
  Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane z
    (Or.inl (near_one_re_pos z hz))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [StarAddMonoid H] [NormedStarGroup H] [StarModule ℂ H]

def multiplier (v : H) : ℂ := (Complex.sqrt (bilinear v v))⁻¹

def normalize (v : H) : H := multiplier v • v

theorem multiplier_ne_zero (v : H) (hv : bilinear v v ≠ 0) : multiplier v ≠ 0 :=
  inv_ne_zero (sqrt_ne_zero _ hv)

theorem multiplier_norm_le (c v : H) (hc : star c = c) (hn : ‖c‖ = 1)
    (hv : ‖v - c‖ ≤ 1 / 5) : ‖multiplier v‖ ≤ 3 / 2 :=
  inv_sqrt_norm_le _ (bilinear_near_unit c v hc hn hv)

theorem bilinear_normalize (v : H) (hv : bilinear v v ≠ 0) : bilinear (normalize v) (normalize v) = 1 := by
  simp only [normalize, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc]
  change (Complex.sqrt (bilinear v v))⁻¹ * (Complex.sqrt (bilinear v v))⁻¹ * bilinear v v = 1
  rw [← mul_inv, ← pow_two, sqrt_sq, inv_mul_cancel₀ hv]

theorem normalize_real_norm (v : H) (hv : star v = v) (hne : v ≠ 0) : ‖normalize v‖ = 1 := by
  have hn := norm_pos_iff.mpr hne
  have hs := sqrt_norm_sq (bilinear v v)
  have hb : ‖bilinear v v‖ = ‖v‖ ^ 2 := by
    rw [bilinear_self_real v hv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖v‖)]
  rw [hb] at hs
  have heq : ‖Complex.sqrt (bilinear v v)‖ = ‖v‖ := by nlinarith [norm_nonneg (Complex.sqrt (bilinear v v))]
  rw [normalize, norm_smul, multiplier, norm_inv, heq, inv_mul_cancel₀ hn.ne']

variable [CompleteSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_normalize {v : E → H} {p : E} (hv : AnalyticAt ℂ v p)
    (hb : ‖bilinear (v p) (v p) - 1‖ ≤ 11 / 25) :
    AnalyticAt ℂ (fun t => normalize (v t)) p := by
  have hs := (analyticAt_sqrt _ hb).comp (f := fun t => bilinear (v t) (v t))
    (analyticAt_bilinear_self hv)
  have hi := hs.inv (sqrt_ne_zero _ (near_one_ne_zero _ hb))
  exact (hi.contDiffAt.smul hv.contDiffAt).analyticAt

#print axioms multiplier_norm_le
#print axioms bilinear_normalize
#print axioms normalize_real_norm
#print axioms analyticAt_normalize

end Maxwell.Continuum.FiberNormalization
