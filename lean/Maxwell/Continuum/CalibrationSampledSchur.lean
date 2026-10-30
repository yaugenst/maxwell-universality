import Maxwell.Continuum.CalibrationResolventCompression
import Maxwell.Continuum.CalibrationSchurApprox
import Maxwell.Continuum.CalibrationInverseError
import Maxwell.Continuum.AuxiliaryFiberInverse

/-! Actual conditioning of the 24 by 24 calibration Schur matrix at
every physical momentum on the cutoff support. Inversion error comes
from the proved continuum resolvent, not a numerical oracle. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber Auxiliary PeriodicBand Metric

attribute [local irreducible] fiberResolvent PeriodicBand.scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState

theorem sampledParameter_bound (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    ∀ j, ‖fiberParameter q j‖ ≤ ((2 : ℝ)^12)⁻¹ :=
  chart_closed_bounds (fiberParameter_chart q hq)

theorem sampledEnergy_norm {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    ‖sampledScaledEnergy z σ‖ ≤ 8 := by
  have hd := sampledScaledEnergy_mem D hσ0 hσ q hq
  rw [mem_closedBall,dist_eq_norm] at hd
  have hb := norm_le_norm_sub_add (sampledScaledEnergy z σ) (scaledBand (fiberParameter q))
  linarith [scaledBand_norm_le (fiberParameter_chart q hq)]

def sampledFullInverse {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    SelfAdjointResolvent.BoundedInverse
      (materialFiber (scaledMomentum (fiberParameter q))
        (totalEnergy (sampledScaledEnergy z σ)) backgroundAmplitude) :=
  transportedInverse (sampledFiber_eq z σ q).symm (fiberInverse D hσ0 hσ q hq)

theorem sampledFullInverse_map {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    (sampledFullInverse D hσ0 hσ q hq).map = fiberResolvent z σ q := by
  rw [sampledFullInverse,transportedInverse_map]
  exact (fiberResolvent_eq_inverse D hσ0 hσ q hq).symm

theorem sampledFullInverse_norm {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    ‖(sampledFullInverse D hσ0 hσ q hq).map‖ ≤ 4*(h^2)⁻¹ := by
  rw [sampledFullInverse_map]
  exact fiberResolvent_norm_le D hσ0 hσ q hq

def sampledSchur {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    centralSpace →L[ℂ] centralSpace :=
  calibrationFiniteSchur (fiberParameter q) (sampledScaledEnergy z σ)
    (sampledParameter_bound q hq) (sampledEnergy_norm D hσ0 hσ q hq)

def sampledSchurApprox {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) (K : ℕ) :
    centralSpace →L[ℂ] centralSpace :=
  calibrationFiniteSchurApprox (fiberParameter q) (sampledScaledEnergy z σ)
    (sampledParameter_bound q hq) (sampledEnergy_norm D hσ0 hσ q hq) K

theorem sampledSchur_isUnit {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    IsUnit (sampledSchur D hσ0 hσ q hq) :=
  calibrationFiniteSchur_isUnit_of_inverse _ _ _ _ (sampledFullInverse D hσ0 hσ q hq)

theorem sampledSchur_inverse_norm {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) :
    ‖Ring.inverse (sampledSchur D hσ0 hσ q hq)‖ ≤ 4*(h^2)⁻¹ :=
  (calibrationFiniteInverse_norm_le _ _ _ _ (sampledFullInverse D hσ0 hσ q hq)).trans
    (sampledFullInverse_norm D hσ0 hσ q hq)

theorem sampledSchurApprox_inverse_error {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4*smallRadius) (K : ℕ)
    (hK : (4*(h^2)⁻¹)*(2*(1/2 : ℝ)^K) ≤ 1/2) :
    IsUnit (sampledSchurApprox D hσ0 hσ q hq K) ∧
      ‖Ring.inverse (sampledSchurApprox D hσ0 hσ q hq K)‖ ≤ 8*(h^2)⁻¹ ∧
      ‖Ring.inverse (sampledSchur D hσ0 hσ q hq)-
        Ring.inverse (sampledSchurApprox D hσ0 hσ q hq K)‖ ≤ 64*(h^4)⁻¹*(1/2 : ℝ)^K := by
  have he := calibrationFiniteSchurApprox_error (fiberParameter q) (sampledScaledEnergy z σ)
    (sampledParameter_bound q hq) (sampledEnergy_norm D hσ0 hσ q hq) K
  have hi := inverse_perturbation_estimate (sampledSchur D hσ0 hσ q hq)
    (sampledSchurApprox D hσ0 hσ q hq K) (sampledSchur_isUnit D hσ0 hσ q hq)
      (sampledSchur_inverse_norm D hσ0 hσ q hq) he hK
  refine ⟨hi.1,hi.2.1.trans_eq (by ring),hi.2.2.trans_eq ?_⟩
  ring

#print axioms sampledSchur_inverse_norm
#print axioms sampledSchurApprox_inverse_error

end Maxwell.Continuum.Calibration
