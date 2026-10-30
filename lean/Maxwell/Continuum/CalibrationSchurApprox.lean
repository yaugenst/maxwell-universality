import Maxwell.Continuum.CalibrationSchur

/-! Finite Neumann evaluation of the actual 24 by 24 Schur matrix.
The infinite-fiber operator error and the finite alias radius are both
proved for the same approximation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)

def calibrationComplementApprox (K : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  calibrationInverseApprox t e ht he K*noncentralAliasProjection

theorem calibrationComplementApprox_error (K : ℕ) :
    ‖calibrationComplementInverse t e ht he-calibrationComplementApprox t e ht he K‖ ≤
      2*(1/2 : ℝ)^K := by
  change ‖(calibrationMaterialInverse t e ht he).map*noncentralAliasProjection-
    calibrationInverseApprox t e ht he K*noncentralAliasProjection‖ ≤ _
  rw [← sub_mul]
  exact (norm_mul_le _ _).trans ((mul_le_mul
    (calibrationInverseApprox_error_dyadic t e ht he K) noncentralAliasProjection_norm
    (norm_nonneg _) (by positivity)).trans_eq (mul_one _))

def calibrationSchurApprox (K : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  calibrationCentralMaterial t e-calibrationLeftCoupling*
    calibrationComplementApprox t e ht he K*calibrationRightCoupling

theorem calibrationSchurApprox_central (K : ℕ) (u : FiberSpace) :
    centralAliasProjection (calibrationSchurApprox t e ht he K u) =
      calibrationSchurApprox t e ht he K u := by
  change centralAliasProjection (calibrationCentralMaterial t e u-
    calibrationLeftCoupling (calibrationComplementApprox t e ht he K (calibrationRightCoupling u))) = _
  rw [map_sub, calibrationCentralMaterial_central, calibrationLeftCoupling_central]
  rfl

theorem calibrationSchurApprox_error (K : ℕ) :
    ‖calibrationSchur t e ht he-calibrationSchurApprox t e ht he K‖ ≤ 2*(1/2 : ℝ)^K := by
  have hl : ‖calibrationLeftCoupling‖ ≤ 1 :=
    calibrationLeftCoupling_norm.trans (calibration_ratio_le_half.trans (by norm_num))
  have hr : ‖calibrationRightCoupling‖ ≤ 1 :=
    calibrationRightCoupling_norm.trans (calibration_ratio_le_half.trans (by norm_num))
  have hid : calibrationSchur t e ht he-calibrationSchurApprox t e ht he K =
      -(calibrationLeftCoupling*(calibrationComplementInverse t e ht he-
        calibrationComplementApprox t e ht he K)*calibrationRightCoupling) := by
    unfold calibrationSchur calibrationSchurApprox
    rw [mul_sub, sub_mul, neg_sub]
    abel
  rw [hid, norm_neg]
  calc
    _ ≤ ‖calibrationLeftCoupling*(calibrationComplementInverse t e ht he-
      calibrationComplementApprox t e ht he K)‖*‖calibrationRightCoupling‖ := norm_mul_le _ _
    _ ≤ (1*(2*(1/2 : ℝ)^K))*1 := mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul hl (calibrationComplementApprox_error t e ht he K) (norm_nonneg _) zero_le_one))
        hr (norm_nonneg _) (by positivity)
    _ = _ := by ring

def calibrationFiniteSchurApprox (K : ℕ) : centralSpace →L[ℂ] centralSpace :=
  restrictCentral (calibrationSchurApprox t e ht he K) (calibrationSchurApprox_central t e ht he K)

theorem calibrationFiniteSchurApprox_error (K : ℕ) :
    ‖calibrationFiniteSchur t e ht he-calibrationFiniteSchurApprox t e ht he K‖ ≤
      2*(1/2 : ℝ)^K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖calibrationSchur t e ht he u.val-calibrationSchurApprox t e ht he K u.val‖ ≤ _
  exact ((calibrationSchur t e ht he-calibrationSchurApprox t e ht he K).le_opNorm u.val).trans
    (mul_le_mul_of_nonneg_right (calibrationSchurApprox_error t e ht he K) (norm_nonneg _))

theorem centralAliasProjection_supported (u : FiberSpace) :
    AliasSupported (centralAliasProjection u) 1 := by
  intro ν hν
  obtain ⟨j,hj⟩ := hν
  have hn : ¬IsCentralAlias ν := by
    intro hc
    rcases hc j with hj0 | hj0 <;> simp only [hj0] at hj <;> norm_num at hj
  simp only [centralAliasProjection_apply, hn, ↓reduceIte]

theorem calibrationRightCoupling_supported (u : FiberSpace) :
    AliasSupported (calibrationRightCoupling u) 2 := by
  exact (centralAliasProjection_supported u).potential.noncentralProjection.smul
    (-(backgroundAmplitude : ℂ))

theorem calibrationSchurApprox_alias_radius (K : ℕ) (u : FiberSpace) :
    AliasSupported (calibrationComplementApprox t e ht he K (calibrationRightCoupling u)) (K+2) := by
  change AliasSupported (calibrationInverseApprox t e ht he K
    (noncentralAliasProjection (calibrationRightCoupling u))) (K+2)
  rw [calibrationRightCoupling_noncentral]
  simpa only [Nat.add_comm] using calibrationInverseApprox_supported
    (calibrationRightCoupling_supported u) t e ht he K

#print axioms calibrationFiniteSchurApprox_error
#print axioms calibrationSchurApprox_alias_radius

end Maxwell.Continuum.Calibration
