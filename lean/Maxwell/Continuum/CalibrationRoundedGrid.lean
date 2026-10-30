import Maxwell.Continuum.CalibrationGridDomain
import Maxwell.Continuum.CalibrationRoundedPrecision
import Maxwell.Continuum.CalibrationRationalFull

/-! Fully rational local inverse coefficients at an accepted Bloch-grid
sample. Its operator error is certified by the actual physical inverse,
including the finite Neumann remainder and the pi evaluation error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber Auxiliary PeriodicBand

attribute [local irreducible] fiberResolvent PeriodicBand.scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState

theorem gridTotalEnergy_bounds {L : ℝ} (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (r : Fin 3 → ℚ) (hr : activeGrid r) :
    (7 : ℝ) ≤ (z+σ+7 : ℚ) ∧ ((z+σ+7 : ℚ) : ℝ) ≤ 8 := by
  simpa only [Rat.cast_add,Rat.cast_ofNat] using
    sampled_totalEnergy_bounds D hσ0 hσ (gridMomentum r) (activeGrid_momentum hr)

def roundedGridFull {L : ℝ} (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (r : Fin 3 → ℚ) (hr : activeGrid r) (K : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  scaledFullApprox (piCenter K) (z+σ+7 : ℚ) (fun j => (r j : ℝ))
    (activeGrid_direction hr) (piCenter_bounds K) (gridTotalEnergy_bounds z σ D hσ0 hσ r hr) K

theorem roundedGridFull_error {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (r : Fin 3 → ℚ) (hr : activeGrid r) (N ell K : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K) :
    IsUnit (scaledFiniteSchurApprox (piCenter K) (z+σ+7 : ℚ) (fun j => (r j : ℝ))
      (activeGrid_direction hr) (piCenter_bounds K) (gridTotalEnergy_bounds z σ D hσ0 hσ r hr) K) ∧
    ‖fiberResolvent z σ (gridMomentum r)-roundedGridFull z σ D hσ0 hσ r hr K‖ ≤ (1/2 : ℝ)^N := by
  have hq := activeGrid_momentum hr
  have hE := gridTotalEnergy_bounds z σ D hσ0 hσ r hr
  have hmom : scaledMomentum (fiberParameter (gridMomentum r)) =
      realMomentum (fun j => Real.pi*(r j : ℝ)) := by
    rw [fiberParameter,scaledMomentum_unscale]
    rfl
  have henergy : totalEnergy (sampledScaledEnergy z σ) = (((z+σ+7 : ℚ) : ℝ) : ℂ) := by
    rw [sampledScaledEnergy,totalEnergy_scaledEnergy]
    simp only [sampledEnergy,Rat.cast_add,Rat.cast_ofNat]
  have hM : 1 ≤ 4*L^2 := by nlinarith [sq_nonneg (L-1)]
  have hR : ‖(sampledFullInverse D hσ0 hσ (gridMomentum r) hq).map‖ ≤ 4*L^2 := by
    simpa only [inv_pow,inv_inv] using sampledFullInverse_norm D hσ0 hσ (gridMomentum r) hq
  have hd : 2*(1/2 : ℝ)^K+32*(|Real.pi-(piCenter K : ℝ)|+
      |((z+σ+7 : ℚ) : ℝ)-((z+σ+7 : ℚ) : ℝ)|) ≤ 4*(1/2 : ℝ)^K := by
    simpa only [sub_self,abs_zero,add_zero] using rounded_inverse_coefficient_error K
  have hb := scaledFullApprox_error (fiberParameter (gridMomentum r)) (sampledScaledEnergy z σ)
    (z+σ+7 : ℚ) (piCenter K) (z+σ+7 : ℚ) (fun j => (r j : ℝ))
    (sampledParameter_bound (gridMomentum r) hq) (sampledEnergy_norm D hσ0 hσ (gridMomentum r) hq)
    (activeGrid_direction hr) hE (piCenter_bounds K) hE hmom henergy
    (sampledFullInverse D hσ0 hσ (gridMomentum r) hq) hM hR K hd
    (rounded_inverse_precision_small hL ell N K hlog hK)
  rw [sampledFullInverse_map] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  convert! rounded_inverse_precision_error hL ell N K hlog hK using 1
  ring

theorem roundedGridFull_represents {L : ℝ} (hL : 1 ≤ L)
    (z σ : ℚ) (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : (0 : ℝ) ≤ σ) (hσ : (σ : ℝ) ≤ (L⁻¹)^4/64)
    (r : Fin 3 → ℚ) (hr : activeGrid r) (N ell K : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K)
    {f : RationalAliasField} {u : FiberSpace} (hf : Represents f u) :
    Represents (rationalFullApply (piCenter K) (z+σ+7) r K f)
      (roundedGridFull z σ D hσ0 hσ r hr K u) :=
  represents_fullApply (piCenter K) (z+σ+7) r (activeGrid_direction hr) (piCenter_bounds K)
    (gridTotalEnergy_bounds z σ D hσ0 hσ r hr) hf K
    (roundedGridFull_error hL z σ D hσ0 hσ r hr N ell K hlog hK).1

#print axioms roundedGridFull_error
#print axioms roundedGridFull_represents

end Maxwell.Continuum.Calibration
