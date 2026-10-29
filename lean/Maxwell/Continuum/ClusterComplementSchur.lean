import Maxwell.Continuum.ClusterComplementLowBlock

/-!
# Exact Schur correction and its uniform norm bound

The correction uses the actual infinite complementary inverse and the
actual two complex off-diagonal couplings. The direct quadratic term is
included. No self-adjoint relation between the complex couplings is assumed.
-/

noncomputable section

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

def scaledLeftCoupling (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : FiberSpace →L[ℂ] FiberSpace :=
  (backgroundAmplitude : ℂ)⁻¹ • leftCoupling t (totalEnergy e) ht

def scaledRightCoupling (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : FiberSpace →L[ℂ] FiberSpace :=
  (backgroundAmplitude : ℂ)⁻¹ • rightCoupling t (totalEnergy e) ht

theorem scaledLeftCoupling_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : ‖scaledLeftCoupling t e ht‖ ≤ 8 := by
  rw [scaledLeftCoupling, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos backgroundAmplitude_pos]
  calc
    _ ≤ backgroundAmplitude⁻¹ * (8 * backgroundAmplitude) :=
      mul_le_mul_of_nonneg_left (leftCoupling_norm_le t (totalEnergy e) ht)
        (inv_nonneg.mpr backgroundAmplitude_pos.le)
    _ = 8 := by field_simp [ne_of_gt backgroundAmplitude_pos]

theorem scaledRightCoupling_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : ‖scaledRightCoupling t e ht‖ ≤ 8 := by
  rw [scaledRightCoupling, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos backgroundAmplitude_pos]
  calc
    _ ≤ backgroundAmplitude⁻¹ * (8 * backgroundAmplitude) :=
      mul_le_mul_of_nonneg_left (rightCoupling_norm_le t (totalEnergy e) ht)
        (inv_nonneg.mpr backgroundAmplitude_pos.le)
    _ = 8 := by field_simp [ne_of_gt backgroundAmplitude_pos]

def schurCorrection (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) : FiberSpace →L[ℂ] FiberSpace :=
  directQuadratic t - scaledLeftCoupling t e ht * complementInverse t e ht he *
    scaledRightCoupling t e ht

theorem schur_self_energy_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖scaledLeftCoupling t e ht * complementInverse t e ht he * scaledRightCoupling t e ht‖ ≤
      128 := by
  calc
    _ ≤ ‖scaledLeftCoupling t e ht * complementInverse t e ht he‖ *
        ‖scaledRightCoupling t e ht‖ := norm_mul_le _ _
    _ ≤ (8 * 2) * 8 := mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul (scaledLeftCoupling_norm_le t e ht)
        (complementInverse_norm_le t e ht he) (norm_nonneg _) (by norm_num)))
      (scaledRightCoupling_norm_le t e ht) (norm_nonneg _) (by norm_num)
    _ = 128 := by norm_num

theorem schurCorrection_norm_lt_129 (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖schurCorrection t e ht he‖ < 129 := by
  exact (norm_sub_le _ _).trans_lt (by
    have hD := directQuadratic_norm_lt_one t ht
    have hS := schur_self_energy_norm_le t e ht he
    linarith)

theorem schurCorrection_norm_le_256 (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖schurCorrection t e ht he‖ ≤ 256 :=
  (schurCorrection_norm_lt_129 t e ht he).le.trans (by norm_num)

def effectiveSchur (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) : FiberSpace →L[ℂ] FiberSpace :=
  leadingCluster t e + (backgroundAmplitude : ℂ) • schurCorrection t e ht he

theorem effectiveSchur_exact (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    (backgroundAmplitude : ℂ) • effectiveSchur t e ht he =
      lowBlock t e - leftCoupling t (totalEnergy e) ht * complementInverse t e ht he *
        rightCoupling t (totalEnergy e) ht := by
  have hρ : (backgroundAmplitude : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt backgroundAmplitude_pos)
  have hcancel : (backgroundAmplitude : ℂ) *
      ((backgroundAmplitude : ℂ) * ((backgroundAmplitude : ℂ)⁻¹ * (backgroundAmplitude : ℂ)⁻¹)) =
      1 := by field_simp
  apply ContinuousLinearMap.ext
  intro u
  change (backgroundAmplitude : ℂ) • (leadingCluster t e u + (backgroundAmplitude : ℂ) •
    (directQuadratic t u - (backgroundAmplitude : ℂ)⁻¹ •
      leftCoupling t (totalEnergy e) ht
        (complementInverse t e ht he ((backgroundAmplitude : ℂ)⁻¹ •
          rightCoupling t (totalEnergy e) ht u)))) =
    ((backgroundAmplitude : ℂ) • leadingCluster t e u +
      (backgroundAmplitude : ℂ) ^ 2 • directQuadratic t u) -
      leftCoupling t (totalEnergy e) ht
        (complementInverse t e ht he (rightCoupling t (totalEnergy e) ht u))
  rw [map_smul, map_smul]
  simp only [smul_add, smul_sub, smul_smul, hcancel, one_smul, pow_two]
  abel

end Maxwell.Continuum.ClusterComplement
