import Maxwell.Continuum.PeriodicBandPhysicalGap
import Maxwell.Continuum.PeriodicBandHessian

/-! The band in physical momentum and dielectric-operator energy units.
The constant dielectric background is subtracted explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Set

def analyticRadius : ℝ := backgroundAmplitude * ((2 : ℝ)^12)⁻¹

def smallRadius : ℝ := backgroundAmplitude * ((2 : ℝ)^40)⁻¹

def quarticConstant : ℝ := 4 * backgroundAmplitude * analyticRadius⁻¹ ^ 4

def physicalChart : Set Momentum := {q | ∀ j, ‖q j‖ < analyticRadius}

def unscale (q : Momentum) : Momentum := (backgroundAmplitude : ℂ)⁻¹ • q

def dielectricBand (q : Momentum) : ℂ := physicalBand (unscale q) - 7

theorem analyticRadius_pos : 0 < analyticRadius :=
  mul_pos backgroundAmplitude_pos (by positivity)

theorem smallRadius_pos : 0 < smallRadius :=
  mul_pos backgroundAmplitude_pos (by positivity)

theorem smallRadius_le_half : smallRadius ≤ analyticRadius / 2 := by
  unfold smallRadius analyticRadius
  have h := mul_le_mul_of_nonneg_left
    (by norm_num : ((2 : ℝ)^40)⁻¹ ≤ ((2 : ℝ)^12)⁻¹ / 2) backgroundAmplitude_pos.le
  nlinarith

theorem scaledMomentum_unscale (q : Momentum) : scaledMomentum (unscale q) = q := by
  have hρ : (backgroundAmplitude : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr backgroundAmplitude_pos.ne'
  funext j
  change (backgroundAmplitude : ℂ) * ((backgroundAmplitude : ℂ)⁻¹ * q j) = q j
  rw [← mul_assoc, mul_inv_cancel₀ hρ, one_mul]

theorem unscale_mem_chart {q : Momentum} (hq : q ∈ physicalChart) : unscale q ∈ chart := by
  intro j
  change ‖(backgroundAmplitude : ℂ)⁻¹ * q j‖ < _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  apply (inv_mul_lt_iff₀ backgroundAmplitude_pos).mpr
  exact hq j

theorem unscale_smul (c : ℂ) (q : Momentum) : unscale (c • q) = c • unscale q := by
  unfold unscale
  rw [smul_comm]

theorem dielectricBand_formula (q : Momentum) :
    dielectricBand q = (((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ) - 7) +
      (backgroundAmplitude : ℂ) * scaledBand (unscale q) := by
  unfold dielectricBand physicalBand totalEnergy
  ring

theorem dielectricBand_analytic : AnalyticOnNhd ℂ dielectricBand physicalChart := by
  intro q hq
  have hu : AnalyticAt ℂ unscale q := by
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := Momentum) (F := Momentum)
      ((backgroundAmplitude : ℂ)⁻¹ • ContinuousLinearMap.id ℂ Momentum) q)
  have hb := AnalyticAt.comp (f := unscale)
    (scaledBand_analytic _ (unscale_mem_chart hq)) hu
  have hf : AnalyticAt ℂ (fun x : Momentum => (((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ) - 7) +
      (backgroundAmplitude : ℂ) * scaledBand (unscale x)) q :=
    (analyticAt_const (v := (((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ) - 7))).add
      ((analyticAt_const (v := (backgroundAmplitude : ℂ))).mul hb)
  have heq : dielectricBand = fun x => (((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ) - 7) +
      (backgroundAmplitude : ℂ) * scaledBand (unscale x) := funext dielectricBand_formula
  rw [heq]
  exact hf

theorem dielectricBand_kernel {q : Momentum} (hq : q ∈ physicalChart) :
    ∃ u : FiberSpace, u ≠ 0 ∧
      (u, 0) ∈ (materialFiber q (dielectricBand q + 7) backgroundAmplitude).graph := by
  have h := actual_band_eigenvector (unscale_mem_chart hq)
  rw [scaledMomentum_unscale] at h
  have hE : dielectricBand q + 7 = totalEnergy (scaledBand (unscale q)) := by
    unfold dielectricBand physicalBand
    ring
  rwa [hE]

end Maxwell.Continuum.PeriodicBand
