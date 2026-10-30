import Maxwell.Continuum.CalibrationSampledSchur
import Maxwell.Continuum.CalibrationFullSupport
import Maxwell.Continuum.CalibrationInversePrecision

/-! The finite local-inverse approximation at the exact physical
calibration energy. The explicit iteration budget controls the operator
error on every alias, and finite inputs have the proved finite output
radius. Elementary rounding and finite quadrature are separate stages. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber Auxiliary PeriodicBand

attribute [local irreducible] fiberResolvent PeriodicBand.scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState

def sampledFullApprox {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) (K : ℕ) :
    FiberSpace →L[ℂ] FiberSpace :=
  calibrationFullApprox (fiberParameter q) (sampledScaledEnergy z σ)
    (sampledParameter_bound q hq) (sampledEnergy_norm D hσ0 hσ q hq) K

theorem sampledFullApprox_requested_error {L z σ : ℝ} (hL : 1 ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) (N ell K : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell) (hK : aliasSteps N ell ≤ K) :
    IsUnit (sampledSchurApprox D hσ0 hσ q hq K) ∧
      ‖fiberResolvent z σ q-sampledFullApprox D hσ0 hσ q hq K‖ ≤ (1/2 : ℝ)^N := by
  have hM : 1 ≤ 4*L^2 := by nlinarith [sq_nonneg (L-1)]
  have hR : ‖(sampledFullInverse D hσ0 hσ q hq).map‖ ≤ 4*L^2 := by
    simpa only [inv_pow,inv_inv] using sampledFullInverse_norm D hσ0 hσ q hq
  have hb := calibrationFullApprox_error (fiberParameter q) (sampledScaledEnergy z σ)
    (sampledParameter_bound q hq) (sampledEnergy_norm D hσ0 hσ q hq)
    (sampledFullInverse D hσ0 hσ q hq) hM hR K (inverse_precision_small hL ell N K hlog hK)
  rw [sampledFullInverse_map] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  convert inverse_precision_error hL ell N K hlog hK using 1
  ring

theorem sampledFullApprox_supported {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) (K : ℕ)
    {u : FiberSpace} {R : ℕ} (hu : AliasSupported u R) :
    AliasSupported (sampledFullApprox D hσ0 hσ q hq K u) (R+2*K+4) :=
  calibrationFullApprox_supported _ _ _ _ hu K

#print axioms sampledFullApprox_requested_error
#print axioms sampledFullApprox_supported

end Maxwell.Continuum.Calibration
