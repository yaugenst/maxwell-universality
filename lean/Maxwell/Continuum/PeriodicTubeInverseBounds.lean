import Maxwell.Continuum.PeriodicTubeResolvent

/-! Quantitative conditioning and holomorphy of the complete fiber
inverse throughout the actual imaginary tube. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic

attribute [local irreducible] fullFiberResolvent fullSpectralProjection separatedSymbol
  dielectricBand shiftedMomentum hessianEnergy

theorem tube_momentum_norm_le {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖shiftedMomentum q b‖ ≤ separatedRadius := by
  calc
    _ ≤ ‖realMomentum q‖ + ‖realMomentum b‖ := shiftedMomentum_norm_le q b
    _ ≤ 4 * smallRadius + 1 / (2 : ℝ)^1024 :=
      add_le_add hq ((tube_shift_norm_le h0 b hb).trans hh)
    _ ≤ _ := by norm_num [smallRadius, separatedRadius, backgroundAmplitude]

theorem fullFiberResolvent_norm_le_pole {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius)
    (hne : dielectricBand q - ((z + σ : ℝ) : ℂ) ≠ 0) :
    ‖fullFiberResolvent z σ q‖ ≤
      ‖(dielectricBand q - ((z + σ : ℝ) : ℂ))⁻¹‖ * (81 / 25) + (2 : ℝ)^112 := by
  rw [fullFiberResolvent_pole_formula D hσ0 hσ hq hne]
  refine (norm_add_le _ _).trans (add_le_add ?_ (separatedSymbol_norm_le D hσ0 hσ hq))
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (fullSpectralProjection_norm_le (separated_unscale_chart hq)) (norm_nonneg _)

theorem fullFiberResolvent_tube_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖fullFiberResolvent z σ (shiftedMomentum q b)‖ ≤ (2 : ℝ)^10 * (h^2)⁻¹ := by
  have hp := fullFiberResolvent_norm_le_pole D hσ0 hσ
    (tube_momentum_norm_le D.h_pos.le hh q b hq hb)
    (tube_denominator_ne_zero D hh hσ q b hq hb)
  have hi := mul_le_mul_of_nonneg_right (tube_inverse_norm_le D hh hσ q b hq hb)
    (by norm_num : (0 : ℝ) ≤ 81 / 25)
  have hs := separated_bound_le_inverse_square D
  calc
    _ ≤ (256 * (h^2)⁻¹) * (81 / 25) + 2 * (h^2)⁻¹ :=
      hp.trans (add_le_add hi hs)
    _ = (256 * (81 / 25 : ℝ) + 2) * (h^2)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr (sq_nonneg h))

theorem fullFiberResolvent_tube_analyticAt {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    AnalyticAt ℂ (fullFiberResolvent z σ) (shiftedMomentum q b) :=
  fullFiberResolvent_analyticAt D hσ0 hσ
    (tube_momentum_norm_le D.h_pos.le hh q b hq hb)
    (tube_denominator_ne_zero D hh hσ q b hq hb)

def tubeFiberInverse {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    SelfAdjointResolvent.BoundedInverse
      (materialFiber (shiftedMomentum q b) (sampledEnergy z σ) backgroundAmplitude) :=
  complexFiberInverse D hσ0 hσ (tube_momentum_norm_le D.h_pos.le hh q b hq hb)
    (tube_denominator_ne_zero D hh hσ q b hq hb)

theorem tubeFiberInverse_map {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    (tubeFiberInverse D hh hσ0 hσ q b hq hb).map =
      fullFiberResolvent z σ (shiftedMomentum q b) :=
  (fullFiberResolvent_eq_inverse D hσ0 hσ
    (tube_momentum_norm_le D.h_pos.le hh q b hq hb)
    (tube_denominator_ne_zero D hh hσ q b hq hb)).symm

theorem tubeFiberInverse_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖(tubeFiberInverse D hh hσ0 hσ q b hq hb).map‖ ≤ (2 : ℝ)^10 * (h^2)⁻¹ := by
  rw [tubeFiberInverse_map]
  exact fullFiberResolvent_tube_norm_le D hh hσ0 hσ q b hq hb

theorem fullFiberResolvent_real (z σ : ℝ) (q : Corner.Vec) :
    fullFiberResolvent z σ (realMomentum q) = fiberResolvent z σ q := by
  unfold fullFiberResolvent fiberResolvent fiberParameter
  rfl

end Maxwell.Continuum.Auxiliary
