import Maxwell.Continuum.EffectiveMassDenominator
import Maxwell.Continuum.WellFourierDecay

/-! Distinct Fourier aliases remain separated after the true momentum
rescaling. This is the geometric input to the off-alias error estimate. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber PeriodicBand

theorem integerVector_norm_ge_one {ν : Alias} (hν : ν ≠ 0) :
    1 ≤ ‖Bloch.integerVector ν‖ := by
  have hj : ∃ j, ν j ≠ 0 := by
    by_contra h
    push Not at h
    apply hν
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hj
  have hi : (1 : ℤ) ≤ |ν j| := Int.one_le_abs hj
  have hi' : (1 : ℝ) ≤ |(ν j : ℝ)| := by exact_mod_cast hi
  have hc := PiLp.norm_apply_le (Bloch.integerVector ν) j
  rw [Bloch.integerVector_apply, Real.norm_eq_abs] at hc
  exact hi'.trans hc

def aliasTransfer (h : ℝ) (p p' : Space) (ν κ : Alias) : Space :=
  p - p' + (Real.pi / h) • Bloch.integerVector (ν - κ)

theorem aliasTransfer_separated {h : ℝ} (hh : 0 < h) (p p' : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) (hp' : h * ‖p'‖ ≤ 4 * smallRadius)
    {ν κ : Alias} (hne : ν ≠ κ) :
    h⁻¹ ≤ ‖aliasTransfer h p p' ν κ‖ := by
  have hlat := integerVector_norm_ge_one (sub_ne_zero.mpr hne)
  have htriangle : ‖(Real.pi / h) • Bloch.integerVector (ν - κ)‖ ≤
      ‖aliasTransfer h p p' ν κ‖ + ‖p - p'‖ := by
    have hv : (Real.pi / h) • Bloch.integerVector (ν - κ) =
        aliasTransfer h p p' ν κ - (p - p') := by unfold aliasTransfer; abel
    rw [hv]
    exact norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos Real.pi_pos hh)] at htriangle
  have hbase := mul_le_mul_of_nonneg_left hlat (div_pos Real.pi_pos hh).le
  have hdiff := norm_sub_le p p'
  have hsmall : 8 * smallRadius ≤ 1 := by norm_num [smallRadius, backgroundAmplitude]
  have hsum : h * ‖p - p'‖ ≤ 8 * smallRadius := by
    nlinarith [mul_le_mul_of_nonneg_left hdiff hh.le]
  rw [← one_div h]
  apply (div_le_iff₀ hh).mpr
  have hm := mul_le_mul_of_nonneg_left htriangle hh.le
  have hm' := mul_le_mul_of_nonneg_left hbase hh.le
  have heq : h * (Real.pi / h * ‖Bloch.integerVector (ν - κ)‖) =
      Real.pi * ‖Bloch.integerVector (ν - κ)‖ := by field_simp
  have heq' : h * (Real.pi / h * 1) = Real.pi := by field_simp
  rw [heq] at hm
  rw [heq, heq'] at hm'
  nlinarith [Real.pi_gt_three]

theorem off_alias_fourier_bound {h : ℝ} (hh : 0 < h) (p p' : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) (hp' : h * ‖p'‖ ≤ 4 * smallRadius)
    {ν κ : Alias} (hne : ν ≠ κ) :
    ‖Well.physicalFourier Well.w (aliasTransfer h p p' ν κ)‖ ≤
      (2 : ℝ)^20 * Real.exp (-1 / (512 * Real.sqrt h)) := by
  have hsep := aliasTransfer_separated hh p p' hp hp' hne
  have hf := Well.well_physicalFourier_decay (aliasTransfer h p p' ν κ)
  have hs := Real.sqrt_le_sqrt hsep
  rw [Real.sqrt_inv] at hs
  have hsr := Real.sqrt_pos.mpr hh
  have he : -Real.sqrt ‖aliasTransfer h p p' ν κ‖ / 256 ≤ -1 / (512 * Real.sqrt h) := by
    have hm := mul_le_mul_of_nonneg_right hs hsr.le
    rw [inv_mul_cancel₀ hsr.ne'] at hm
    field_simp
    nlinarith
  exact (le_trans (le_add_of_nonneg_right (norm_nonneg _)) hf).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity))

end Maxwell.Continuum.EffectiveMass
