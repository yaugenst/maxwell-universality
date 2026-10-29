import Maxwell.Continuum.AuxiliaryEnergy
import Maxwell.Continuum.PeriodicHessianError

/-! The actual normalized continuum dispersion denominator and its
quantitative comparison with the proved effective Hessian. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber PeriodicBand Auxiliary

def physicalMomentum (p : Space) : Momentum := realMomentum p.ofLp

theorem space_dot_self (p : Space) : dotProduct p.ofLp p.ofLp = ‖p‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, Real.norm_eq_abs, pow_two]

theorem physicalMomentum_norm_le (p : Space) : ‖physicalMomentum p‖ ≤ ‖p‖ := by
  have h := norm_realMomentum_sq_le_dot p.ofLp
  rw [space_dot_self] at h
  change ‖physicalMomentum p‖^2 ≤ ‖p‖^2 at h
  nlinarith [norm_nonneg p, norm_nonneg (physicalMomentum p)]

def quadratic (p : Space) : ℝ := inner ℝ p (hessianOperator p)

theorem quadratic_nonneg (p : Space) : 0 ≤ quadratic p := hessianOperator_nonneg p

theorem quadratic_smul (h : ℝ) (p : Space) : quadratic (h • p) = h^2 * quadratic p := by
  simp only [quadratic, map_smul, inner_smul_left, inner_smul_right, conj_trivial]
  ring

def bandValue (p : Space) : ℝ := (dielectricBand (physicalMomentum p)).re

theorem bandValue_curvature (p : Space) (hp : ‖p‖ ≤ 4 * smallRadius) :
    quadratic p / 2 ≤ bandValue p - centerEnergy ∧
      bandValue p - centerEnergy ≤ (3 / 2 : ℝ) * quadratic p := by
  have h := physical_small_curvature p.ofLp ((physicalMomentum_norm_le p).trans hp)
  simpa only [quadratic, hessianOperator_inner, bandValue, physicalMomentum,
    centerEnergy, one_div, div_eq_mul_inv, one_mul, mul_comm] using h

theorem bandValue_quartic (p : Space) (hp : ‖p‖ ≤ analyticRadius / 2) :
    |bandValue p - centerEnergy - quadratic p| ≤ quarticConstant * ‖p‖^4 := by
  have h := (Complex.abs_re_le_norm
    (dielectricBand (physicalMomentum p) - dielectricBand 0 -
      physicalQuadratic (physicalMomentum p))).trans
        (physical_quartic ((physicalMomentum_norm_le p).trans hp))
  rw [show physicalMomentum p = realMomentum p.ofLp from rfl,
    physicalQuadratic_real_form] at h
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  change |bandValue p - centerEnergy - dotProduct p.ofLp (hessian.mulVec p.ofLp)| ≤
    quarticConstant * ‖physicalMomentum p‖^4 at h
  rw [← hessianOperator_inner] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (physicalMomentum_norm_le p) 4) quarticConstant_nonneg)

def referenceDenominator (p : Space) : ℝ := 1 + quadratic p

def bandDenominator (h z : ℝ) (p : Space) : ℝ := (bandValue (h • p) - z) / h^2

theorem referenceDenominator_ge_one (p : Space) : 1 ≤ referenceDenominator p := by
  unfold referenceDenominator
  linarith [quadratic_nonneg p]

theorem scaled_norm {h : ℝ} (hh : 0 ≤ h) (p : Space) : ‖h • p‖ = h * ‖p‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]

theorem bandDenominator_lower {h z : ℝ} (D : Calibration h z)
    (p : Space) (hp : h * ‖p‖ ≤ 4 * smallRadius) :
    referenceDenominator p / 2 ≤ bandDenominator h z p := by
  have hcurv := (bandValue_curvature (h • p) (by rwa [scaled_norm D.h_pos.le])).1
  rw [quadratic_smul] at hcurv
  have he := (abs_le.mp D.error).2
  have hh := calibration_h_small D
  have h2 : h^2 ≤ (1 / 2 : ℝ) := by nlinarith [D.h_pos]
  have h4 : h^4 ≤ h^2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg h)]
  apply (le_div_iff₀ (sq_pos_of_pos D.h_pos)).mpr
  change (1 + quadratic p) / 2 * h^2 ≤ bandValue (h • p) - z
  nlinarith

theorem bandDenominator_error {h z : ℝ} (D : Calibration h z)
    (p : Space) (hp : h * ‖p‖ ≤ 4 * smallRadius) :
    |bandDenominator h z p - referenceDenominator p| ≤
      h^2 * (1 + quarticConstant * ‖p‖^4) := by
  have hnorm : ‖h • p‖ ≤ analyticRadius / 2 := by
    rw [scaled_norm D.h_pos.le]
    exact hp.trans four_smallRadius_le_half
  have hb := bandValue_quartic (h • p) hnorm
  rw [quadratic_smul, scaled_norm D.h_pos.le, mul_pow] at hb
  have he := abs_le.mp D.error
  have hb' := abs_le.mp hb
  have hpos := sq_pos_of_pos D.h_pos
  rw [bandDenominator, div_sub' hpos.ne', abs_div, abs_of_pos hpos,
    div_le_iff₀ hpos]
  unfold referenceDenominator
  apply abs_le.mpr
  constructor
  · nlinarith [hb'.1, he.2]
  · nlinarith [hb'.2, he.1]

end Maxwell.Continuum.EffectiveMass
