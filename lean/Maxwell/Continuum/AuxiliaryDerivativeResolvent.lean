import Maxwell.Continuum.AuxiliaryLocalInverse
import Maxwell.Continuum.PeriodicMaterialDerivative

/-! The derivative resolvent is the actual product of two local inverses
and the literal dielectric derivative, with exactly one smooth cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber FiberAnalytic Bloch MeasureTheory

attribute [local irreducible] localInverse Auxiliary.resolvent cutoffFiber fiberResolvent

def derivativeResolvent {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (j : Fin 3) : FieldL2 →L[ℂ] FieldL2 :=
  localInverse D hσ0 hσ * PeriodicMaterial.derivativeMultiplier j * resolvent D hσ0 hσ

def derivativeResolventFiber (z σ : ℝ) (j : Fin 3) (q : QuasiCell) : FiberMap :=
  localInverseFiber z σ q * PeriodicMaterial.derivativeFiber j * cutoffFiber z σ q

theorem derivativeResolvent_ae {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (j : Fin 3) (f : FieldL2) :
    unitary (derivativeResolvent D hσ0 hσ j f) =ᵐ[quasiMeasure]
      fun q => derivativeResolventFiber z σ j q (unitary f q) := by
  filter_upwards [localInverse_ae D hσ0 hσ
    (PeriodicMaterial.derivativeMultiplier j (resolvent D hσ0 hσ f)),
    PeriodicMaterial.unitary_derivativeMultiplier_ae j (resolvent D hσ0 hσ f),
    resolvent_ae D hσ0 hσ f] with q hl hd hr
  change unitary (localInverse D hσ0 hσ
    (PeriodicMaterial.derivativeMultiplier j (resolvent D hσ0 hσ f))) q = _
  rw [hl, hd, hr]
  rfl

theorem derivativeResolventFiber_one_cutoff (z σ : ℝ) (j : Fin 3) (q : QuasiCell) :
    derivativeResolventFiber z σ j q = (cutoff q.val : ℂ) •
      (localInverseFiber z σ q * PeriodicMaterial.derivativeFiber j * localInverseFiber z σ q) := by
  apply ContinuousLinearMap.ext
  intro f
  change localInverseFiber z σ q (PeriodicMaterial.derivativeFiber j (cutoffFiber z σ q f)) = _
  rw [cutoffFiber_eq_local, smul_apply, map_smul, map_smul]
  rfl

theorem cutoffOperator_derivativeMultiplier (j : Fin 3) :
    cutoffOperator * PeriodicMaterial.derivativeMultiplier j =
      PeriodicMaterial.derivativeMultiplier j * cutoffOperator := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitary.injective
  apply Lp.ext
  filter_upwards [cutoffOperator_ae (PeriodicMaterial.derivativeMultiplier j f),
    PeriodicMaterial.unitary_derivativeMultiplier_ae j f,
    PeriodicMaterial.unitary_derivativeMultiplier_ae j (cutoffOperator f),
    cutoffOperator_ae f] with q hc hd hdc hcf
  change unitary (cutoffOperator (PeriodicMaterial.derivativeMultiplier j f)) q =
    unitary (PeriodicMaterial.derivativeMultiplier j (cutoffOperator f)) q
  rw [hc, hd, hdc, hcf, map_smul]

/-- The exact formula in the paper, with χ occurring once. -/
theorem derivativeResolvent_one_cutoff {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (j : Fin 3) :
    derivativeResolvent D hσ0 hσ j = cutoffOperator * localInverse D hσ0 hσ *
      PeriodicMaterial.derivativeMultiplier j * localInverse D hσ0 hσ := by
  unfold derivativeResolvent
  rw [resolvent_eq_cutoff_local]
  have he := (resolvent_eq_local_cutoff D hσ0 hσ).symm.trans (resolvent_eq_cutoff_local D hσ0 hσ)
  calc
    _ = localInverse D hσ0 hσ * (PeriodicMaterial.derivativeMultiplier j * cutoffOperator) *
        localInverse D hσ0 hσ := by noncomm_ring
    _ = localInverse D hσ0 hσ * (cutoffOperator * PeriodicMaterial.derivativeMultiplier j) *
        localInverse D hσ0 hσ := by rw [cutoffOperator_derivativeMultiplier]
    _ = (localInverse D hσ0 hσ * cutoffOperator) * PeriodicMaterial.derivativeMultiplier j *
        localInverse D hσ0 hσ := by noncomm_ring
    _ = _ := by rw [he]

theorem derivativeResolvent_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (j : Fin 3) :
    ‖derivativeResolvent D hσ0 hσ j‖ ≤ 448 * (h^4)⁻¹ := by
  unfold derivativeResolvent
  calc
    _ ≤ (‖localInverse D hσ0 hσ‖ * ‖PeriodicMaterial.derivativeMultiplier j‖) *
        ‖resolvent D hσ0 hσ‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ ((4*(h^2)⁻¹) * 28) * (4*(h^2)⁻¹) :=
      mul_le_mul (mul_le_mul (localInverse_norm_le D hσ0 hσ)
        (PeriodicMaterial.derivativeMultiplier_norm_le j) (norm_nonneg _) (by positivity))
        (resolvent_norm_le D hσ0 hσ) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [← inv_pow]; ring

#print axioms derivativeResolvent_one_cutoff
#print axioms derivativeResolvent_norm_le

end Maxwell.Continuum.Auxiliary
