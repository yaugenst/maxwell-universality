import Maxwell.Continuum.ClusterComplementCouplingBounds
import Maxwell.Continuum.ClusterComplementEquations

/-!
# Literal cluster--complement couplings

The bounded maps below are the actual off-diagonal compressions of the
complex Maxwell fiber. Both are bounded by `8 ρ`; they are not identified
as adjoints at complex momentum.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

theorem block_corner (s : Fin 3 → ℝ) (c E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) :
    block (c • realMomentum s) E =
      (3 * c ^ 2 - E) • (1 : Polarization →L[ℂ] Polarization) - (3 * c ^ 2) • longitudinal s := by
  have hs' : momentumSquare (realMomentum s) = 3 := by rw [momentumSquare_real, hs]; norm_num
  rw [block, blockMatrix, momentumSquare_smul, momentumOuter_smul, hs',
    matrixCLM_sub, matrixCLM_smul, matrixCLM_smul, matrixCLM_one_eq,
    longitudinal, longitudinalMatrix, matrixCLM_smul, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem projection_polynomial_left (L : Polarization →L[ℂ] Polarization)
    (hL : L * L = L) (a b : ℂ) : (1 - L) * (a • 1 - b • L) * L = 0 := by
  have hLv (v : Polarization) : L (L v) = L v :=
    congrArg (fun T : Polarization →L[ℂ] Polarization => T v) hL
  apply ContinuousLinearMap.ext
  intro v
  change (a • L v - b • L (L v)) - L (a • L v - b • L (L v)) = 0
  simp only [map_sub, map_smul, hLv, sub_self]

theorem projection_polynomial_right (L : Polarization →L[ℂ] Polarization)
    (hL : L * L = L) (a b : ℂ) : L * (a • 1 - b • L) * (1 - L) = 0 := by
  have hLv (v : Polarization) : L (L v) = L v :=
    congrArg (fun T : Polarization →L[ℂ] Polarization => T v) hL
  apply ContinuousLinearMap.ext
  intro v
  change L (a • (v - L v) - b • L (v - L v)) = 0
  simp only [map_sub, map_smul, hLv, sub_self, smul_zero, map_zero]

theorem baseMomentum_corner (ν : Alias) :
    realMomentum (baseMomentum ν) = ((Real.pi : ℂ) / 2) • realMomentum (cornerSigns ν) := by
  funext j
  simp only [realMomentum, baseMomentum, cornerSigns, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem base_left_coupling_zero (E : ℂ) (ν : Alias) :
    clusterBlock ν * block (realMomentum (baseMomentum ν)) E * complementBlock ν = 0 := by
  by_cases hν : IsCentralAlias ν
  · rw [clusterBlock_central ν hν, complementBlock_central ν hν,
      baseMomentum_corner, block_corner _ _ _ (cornerSigns_norm_sq ν hν)]
    exact projection_polynomial_left _
      (longitudinal_isStarProjection _ (cornerSigns_norm_sq ν hν)).isIdempotentElem.eq _ _
  · rw [clusterBlock_noncentral ν hν, zero_mul, zero_mul]

theorem base_right_coupling_zero (E : ℂ) (ν : Alias) :
    complementBlock ν * block (realMomentum (baseMomentum ν)) E * clusterBlock ν = 0 := by
  by_cases hν : IsCentralAlias ν
  · rw [clusterBlock_central ν hν, complementBlock_central ν hν,
      baseMomentum_corner, block_corner _ _ _ (cornerSigns_norm_sq ν hν)]
    exact projection_polynomial_right _
      (longitudinal_isStarProjection _ (cornerSigns_norm_sq ν hν)).isIdempotentElem.eq _ _
  · rw [clusterBlock_noncentral ν hν, mul_zero]

def freeLeftCouplingBlock (t : Momentum) (E : ℂ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  clusterBlock ν * block (aliasMomentum (scaledMomentum t) ν) E * complementBlock ν

def freeRightCouplingBlock (t : Momentum) (E : ℂ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  complementBlock ν * block (aliasMomentum (scaledMomentum t) ν) E * clusterBlock ν

theorem contraction_sandwich_norm_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P T Q : H →L[ℂ] H) (hP : ‖P‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) : ‖P * T * Q‖ ≤ ‖T‖ := by
  calc
    ‖P * T * Q‖ ≤ ‖P * T‖ * ‖Q‖ := norm_mul_le _ _
    _ ≤ (1 * ‖T‖) * 1 := mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _)))
      hQ (norm_nonneg _) (by positivity)
    _ = ‖T‖ := by ring

theorem freeLeftCouplingBlock_norm_le (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (ν : Alias) :
    ‖freeLeftCouplingBlock t E ν‖ ≤ backgroundAmplitude / 32 := by
  by_cases hν : IsCentralAlias ν
  · have heq : freeLeftCouplingBlock t E ν = clusterBlock ν *
        (block (aliasMomentum (scaledMomentum t) ν) E - block (realMomentum (baseMomentum ν)) E) *
        complementBlock ν := by
      rw [mul_sub, sub_mul, base_left_coupling_zero, sub_zero]
      rfl
    rw [heq]
    exact (contraction_sandwich_norm_le _ _ _ (clusterBlock_norm_le ν)
      (complementBlock_norm_le ν)).trans (central_block_variation_norm_le t E ν ht hν)
  · simp only [freeLeftCouplingBlock, clusterBlock_noncentral ν hν, zero_mul, norm_zero]
    exact div_nonneg backgroundAmplitude_pos.le (by norm_num)

theorem freeRightCouplingBlock_norm_le (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (ν : Alias) :
    ‖freeRightCouplingBlock t E ν‖ ≤ backgroundAmplitude / 32 := by
  by_cases hν : IsCentralAlias ν
  · have heq : freeRightCouplingBlock t E ν = complementBlock ν *
        (block (aliasMomentum (scaledMomentum t) ν) E - block (realMomentum (baseMomentum ν)) E) *
        clusterBlock ν := by
      rw [mul_sub, sub_mul, base_right_coupling_zero, sub_zero]
      rfl
    rw [heq]
    exact (contraction_sandwich_norm_le _ _ _ (complementBlock_norm_le ν)
      (clusterBlock_norm_le ν)).trans (central_block_variation_norm_le t E ν ht hν)
  · simp only [freeRightCouplingBlock, clusterBlock_noncentral ν hν, mul_zero, norm_zero]
    exact div_nonneg backgroundAmplitude_pos.le (by norm_num)

def freeLeftCoupling (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (freeLeftCouplingBlock t E) (div_nonneg backgroundAmplitude_pos.le (by norm_num))
    (freeLeftCouplingBlock_norm_le t E ht)

def freeRightCoupling (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (freeRightCouplingBlock t E) (div_nonneg backgroundAmplitude_pos.le (by norm_num))
    (freeRightCouplingBlock_norm_le t E ht)

theorem freeLeftCoupling_norm_le (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖freeLeftCoupling t E ht‖ ≤ backgroundAmplitude / 32 := boundedBlocks_norm_le _ _ _

theorem freeRightCoupling_norm_le (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖freeRightCoupling t E ht‖ ≤ backgroundAmplitude / 32 := boundedBlocks_norm_le _ _ _

def leftCoupling (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : FiberSpace →L[ℂ] FiberSpace :=
  freeLeftCoupling t E ht - (backgroundAmplitude : ℂ) •
    (clusterProjection * potential * complementProjection)

def rightCoupling (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : FiberSpace →L[ℂ] FiberSpace :=
  freeRightCoupling t E ht - (backgroundAmplitude : ℂ) •
    (complementProjection * potential * clusterProjection)

theorem leftCoupling_norm_le (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖leftCoupling t E ht‖ ≤ 8 * backgroundAmplitude := by
  have hp := (contraction_sandwich_norm_le clusterProjection potential complementProjection
    clusterProjection_norm_le complementProjection_norm_le).trans potential_norm_le
  have h := norm_sub_le (freeLeftCoupling t E ht)
    ((backgroundAmplitude : ℂ) • (clusterProjection * potential * complementProjection))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos] at h
  unfold leftCoupling
  nlinarith [freeLeftCoupling_norm_le t E ht,
    mul_le_mul_of_nonneg_left hp backgroundAmplitude_pos.le, backgroundAmplitude_pos]

theorem rightCoupling_norm_le (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    ‖rightCoupling t E ht‖ ≤ 8 * backgroundAmplitude := by
  have hp := (contraction_sandwich_norm_le complementProjection potential clusterProjection
    complementProjection_norm_le clusterProjection_norm_le).trans potential_norm_le
  have h := norm_sub_le (freeRightCoupling t E ht)
    ((backgroundAmplitude : ℂ) • (complementProjection * potential * clusterProjection))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos] at h
  unfold rightCoupling
  nlinarith [freeRightCoupling_norm_le t E ht,
    mul_le_mul_of_nonneg_left hp backgroundAmplitude_pos.le, backgroundAmplitude_pos]

theorem leftCoupling_apply (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (u : (operator (scaledMomentum t) E).domain) :
    leftCoupling t E ht u.val = clusterProjection
      (materialFiber (scaledMomentum t) E backgroundAmplitude
        ⟨complementProjection u.val, complementProjection_mem_domain _ _ u⟩) := by
  rw [materialFiber_apply, map_sub, map_smul]
  change freeLeftCoupling t E ht u.val - (backgroundAmplitude : ℂ) •
    clusterProjection (potential (complementProjection u.val)) = _
  congr 1

theorem rightCoupling_apply (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (u : FiberSpace) :
    rightCoupling t E ht u = complementProjection
      (materialFiber (scaledMomentum t) E backgroundAmplitude
        ⟨clusterProjection u, clusterProjection_mem_domain _ _ u⟩) := by
  rw [materialFiber_apply, map_sub, map_smul]
  change freeRightCoupling t E ht u - (backgroundAmplitude : ℂ) •
    complementProjection (potential (clusterProjection u)) = _
  congr 1

end Maxwell.Continuum.ClusterComplement
