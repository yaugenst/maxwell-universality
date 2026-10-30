import Maxwell.Continuum.CalibrationPowerBasic

/-! Quantitative normalization stability and convergence of the actual
power iterates, including their nonzero lower norm. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open TopEigenPerturbation NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem normalize_difference (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖normalize x-normalize y‖ ≤ 2*‖x-y‖/‖y‖ := by
  have hr : 0 < ‖y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hy)
  have hb := normalize_sub_unit (‖y‖⁻¹ • x) (normalize y)
    (smul_ne_zero hr.ne' hx) (norm_normalize hy)
  rw [normalize_smul_of_pos hr] at hb
  have he : ‖y‖⁻¹ • x-normalize y = ‖y‖⁻¹ • (x-y) := by
    rw [smul_sub]
    rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hb
  exact hb.trans_eq (by ring)

variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

theorem normalized_power_error (v : H) (hv : inner ℂ u v ≠ 0) (n : ℕ) :
    ‖normalize ((A^n) v)-normalize (inner ℂ u v • u)‖ ≤
      2*(mu-d)^n*‖v‖/(mu^n*‖inner ℂ u v‖) := by
  have hm : 0 < mu := lt_of_lt_of_le D.gap_pos D.gap_le_mu
  have hu : u ≠ 0 := by intro hz; have hn := D.unit_norm; rw [hz,norm_zero] at hn; norm_num at hn
  have hy : (mu : ℂ)^n • (inner ℂ u v • u) ≠ 0 :=
    smul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hm.ne')) (smul_ne_zero hv hu)
  have he : (mu : ℂ)^n • (inner ℂ u v • u) = (mu^n : ℝ) • (inner ℂ u v • u) := by
    rw [← Complex.ofReal_pow, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hb := normalize_difference ((A^n) v) ((mu : ℂ)^n • (inner ℂ u v • u))
    (power_ne_zero D v hv n) hy
  rw [he, normalize_smul_of_pos (pow_pos hm n)] at hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hm n), norm_smul, D.unit_norm,
    mul_one] at hb
  have hp := power_error D v n
  rw [he] at hp
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (mul_nonneg (pow_nonneg hm.le n) (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

theorem normalized_power_error_ratio (v : H) (hv : inner ℂ u v ≠ 0) (n : ℕ)
    {r : ℝ} (hgap : mu-d ≤ mu*r) :
    ‖normalize ((A^n) v)-normalize (inner ℂ u v • u)‖ ≤
      2*r^n*‖v‖/‖inner ℂ u v‖ := by
  have hm : 0 < mu := lt_of_lt_of_le D.gap_pos D.gap_le_mu
  have hc : 0 < ‖inner ℂ u v‖ := norm_pos_iff.mpr hv
  apply (normalized_power_error D v hv n).trans
  calc
    _ ≤ 2*(mu*r)^n*‖v‖/(mu^n*‖inner ℂ u v‖) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (sub_nonneg.mpr D.gap_le_mu) hgap n) (by norm_num)) (norm_nonneg _))
      (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

theorem normalized_power_error_real_overlap (v : H) (n : ℕ) {a r : ℝ}
    (ha : 0 < a) (hc : inner ℂ u v = (a : ℂ)) (hgap : mu-d ≤ mu*r) :
    ‖normalize ((A^n) v)-u‖ ≤ 2*r^n*‖v‖/a := by
  have hv : inner ℂ u v ≠ 0 := by rw [hc]; exact Complex.ofReal_ne_zero.mpr ha.ne'
  have hb := normalized_power_error_ratio D v hv n hgap
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hb
  have he : (a : ℂ) • u = a • u := (RCLike.real_smul_eq_coe_smul (K := ℂ) a u).symm
  rw [he, normalize_smul_of_pos ha, normalize_eq_self_of_norm_eq_one D.unit_norm] at hb
  exact hb

theorem normalized_approximate_power_error (v : H) (hv : inner ℂ u v ≠ 0)
    (y : H) (hy : y ≠ 0) (n : ℕ) {ε : ℝ} (hε : ‖y-(A^n) v‖ ≤ ε) :
    ‖normalize y-normalize ((A^n) v)‖ ≤ 2*ε/(mu^n*‖inner ℂ u v‖) := by
  have hm : 0 < mu := lt_of_lt_of_le D.gap_pos D.gap_le_mu
  have hp : 0 < mu^n*‖inner ℂ u v‖ := mul_pos (pow_pos hm n) (norm_pos_iff.mpr hv)
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hb := normalize_difference y ((A^n) v) hy (power_ne_zero D v hv n)
  apply hb.trans
  apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hε (by norm_num)) hp
  exact power_norm_lower D v n

#print axioms normalized_power_error_ratio
#print axioms normalized_approximate_power_error

end Maxwell.Continuum.Calibration
