import Maxwell.Continuum.FiniteAuxiliaryIdealSource

/-! A nonzero quantitative source norm from the actual local eigenvalue
equation. A simple operator estimate already suffices for the paper's
source lower bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh

theorem localSource_norm_lower {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    1/(2 : ℝ)^130 ≤ ‖localSource D hh‖ := by
  have hp := D.h_pos
  have hμ := muH_pos D hh
  have he : ‖Sh D (realMode D hh)‖ = muH D hh := by
    rw [realMode_eigen, norm_smul, Complex.norm_real, Real.norm_of_nonneg hμ.le,
      realMode_norm, mul_one]
  have hq := (Qh h).le_of_opNorm_le (Qh_norm_le h)
    (resolvent D le_rfl (by positivity) (localSource D hh))
  have hr := (resolvent D le_rfl (by positivity)).le_of_opNorm_le
    (resolvent_norm_le D le_rfl (by positivity)) (localSource D hh)
  rw [one_mul] at hq
  have hb : muH D hh ≤ (4*(h^2)⁻¹)*‖localSource D hh‖ := by
    rw [← he, Sh]
    exact hq.trans hr
  have hlo := (muH_bounds D hh).1.trans hb
  have hscaled : (h^2)⁻¹*(1/(2 : ℝ)^128) ≤ (h^2)⁻¹*(4*‖localSource D hh‖) := by
    convert hlo using 1 <;> ring
  have hc := (mul_le_mul_iff_right₀ (inv_pos.mpr (pow_pos hp 2))).mp hscaled
  norm_num at hc ⊢
  linarith only [hc]

theorem muH_inverse_lower {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    h^2 ≤ (muH D hh)⁻¹ := by
  have hp := D.h_pos
  have hb : muH D hh ≤ (h^2)⁻¹ := (muH_bounds D hh).2.trans (by
    apply mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg h))
    norm_num)
  have hi := (inv_le_inv₀ (inv_pos.mpr (pow_pos hp 2)) (muH_pos D hh)).mpr hb
  simpa only [inv_inv] using hi

variable {ι : Type*} [Fintype ι]

theorem idealSource_norm_lower {h z α : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (hα : 0 ≤ α)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (g : BrightSpace ι) : (1/(2 : ℝ)^256)*α*h^2*‖g‖ ≤ ‖idealSource D hh r α g‖ := by
  rw [idealSource_norm D hh r hα hdisj g, div_eq_mul_inv]
  have hp := D.h_pos
  have hμ := muH_pos D hh
  calc
    _ ≤ (α*h^2)*(1/(2 : ℝ)^130)*‖g‖ := by
      have hc : (1/(2 : ℝ)^256) ≤ 1/(2 : ℝ)^130 := by norm_num
      have hs := mul_le_mul_of_nonneg_right hc (show 0 ≤ α*h^2*‖g‖ by positivity)
      convert hs using 1 <;> ring
    _ ≤ (α*(muH D hh)⁻¹)*‖localSource D hh‖*‖g‖ := by
      gcongr
      · exact muH_inverse_lower D hh
      · exact localSource_norm_lower D hh

#print axioms idealSource_norm_lower

end Maxwell.Continuum.FiniteAuxiliary
