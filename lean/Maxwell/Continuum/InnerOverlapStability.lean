import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Linarith

/-! Quantitative stability and normalization of a positive real overlap. -/

noncomputable section

namespace Maxwell.Continuum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_re_lower_left (u v w : H) :
    (inner ℂ u w).re - ‖u-v‖ * ‖w‖ ≤ (inner ℂ v w).re := by
  have h := (Complex.re_le_norm (inner ℂ (u-v) w)).trans (norm_inner_le_norm (u-v) w)
  rw [inner_sub_left, Complex.sub_re] at h
  linarith

theorem inner_re_lower_right (u v w : H) :
    (inner ℂ u v).re - ‖u‖ * ‖v-w‖ ≤ (inner ℂ u w).re := by
  have h := (Complex.re_le_norm (inner ℂ u (v-w))).trans (norm_inner_le_norm u (v-w))
  rw [inner_sub_right, Complex.sub_re] at h
  linarith

theorem normalize_inner_re (u v : H) :
    (inner ℂ (NormedSpace.normalize u) v).re = ‖u‖⁻¹ * (inner ℂ u v).re := by
  rw [NormedSpace.normalize, ← algebraMap_smul ℂ, inner_smul_real_left]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem normalized_overlap_lower {u v : H} {c C : ℝ}
    (hc : 0 < c) (_hC : 0 < C) (hu : ‖u‖ ≤ C) (he : c ≤ (inner ℂ u v).re) :
    c / C ≤ (inner ℂ (NormedSpace.normalize u) v).re := by
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at he
    change c ≤ 0 at he
    exact (not_le.mpr hc) he
  have hn := norm_pos_iff.mpr hu0
  rw [normalize_inner_re]
  calc
    _ ≤ c / ‖u‖ := div_le_div_of_nonneg_left hc.le hn hu
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hn.le)
      simpa only [div_eq_mul_inv, mul_comm c] using hm

end Maxwell.Continuum
