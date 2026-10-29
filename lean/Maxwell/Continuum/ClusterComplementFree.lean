import Maxwell.Continuum.ClusterComplementProjection

/-!
# Infinite fixed-complement free inverse

The operator is `Q A(q,E) Q + P`, with identity on the fixed cluster. Its
maximal domain is proved equal to the actual free-fiber domain at this
momentum. The inverse contains all central longitudinal and noncentral modes.
-/

noncomputable section

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber SelfAdjointResolvent
open scoped Classical

def regularizedBlock (t : Momentum) (e : ℂ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  complementBlock ν * block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e) *
    complementBlock ν + clusterBlock ν

def regularizedInverseBlock (t : Momentum) (e : ℂ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then
    centralRegularizedInverse (cornerSigns ν) (scaledMomentum t) (totalEnergy e)
  else inverseBlock (aliasMomentum (scaledMomentum t) ν) (totalEnergy e)

theorem regularizedBlock_central (t : Momentum) (e : ℂ) (ν : Alias) (hν : IsCentralAlias ν) :
    regularizedBlock t e ν = centralRegularizedBlock (cornerSigns ν) (scaledMomentum t)
      ((Real.pi : ℂ) / 2) (totalEnergy e) := by
  rw [regularizedBlock, complementBlock_central ν hν, clusterBlock_central ν hν,
    central_momentum_decomposition]
  rfl

theorem regularizedBlock_noncentral (t : Momentum) (e : ℂ) (ν : Alias) (hν : ¬IsCentralAlias ν) :
    regularizedBlock t e ν = block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e) := by
  simp only [regularizedBlock, complementBlock_noncentral ν hν, clusterBlock_noncentral ν hν,
    one_mul, mul_one, add_zero]

theorem regularizedInverseBlock_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (ν : Alias) :
    ‖regularizedInverseBlock t e ν‖ ≤ 6 / 5 := by
  by_cases hν : IsCentralAlias ν
  · rw [regularizedInverseBlock, ite_eq_left hν]
    exact centralRegularizedInverse_norm_le _ _ _ (cornerSigns_norm_sq ν hν)
      (scaledMomentum_norm_le t ht) (totalEnergy_norm_bounds e he).1
  · rw [regularizedInverseBlock, ite_eq_right hν]
    exact (noncentral_inverse_estimate t e ν ht he hν).2.2.trans (by norm_num)

theorem regularizedBlock_inverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (ν : Alias) (v : Polarization) :
    regularizedBlock t e ν (regularizedInverseBlock t e ν v) = v := by
  by_cases hν : IsCentralAlias ν
  · have hd := longitudinal_denominator_norm (cornerSigns ν) (scaledMomentum t) (totalEnergy e)
      (cornerSigns_norm_sq ν hν) (scaledMomentum_norm_le t ht) (totalEnergy_norm_bounds e he).1
    have hd0 : longitudinalDenominator (cornerSigns ν) (scaledMomentum t) (totalEnergy e) ≠ 0 :=
      norm_pos_iff.mp (by linarith)
    rw [regularizedBlock_central t e ν hν, regularizedInverseBlock, ite_eq_left hν]
    exact central_regularized_inverse_left_apply (cornerSigns ν) (scaledMomentum t)
      ((Real.pi : ℂ) / 2) (totalEnergy e) (cornerSigns_norm_sq ν hν) hd0 v
  · rw [regularizedBlock_noncentral t e ν hν, regularizedInverseBlock, ite_eq_right hν]
    exact block_inverseBlock _ _ (noncentral_inverse_estimate t e ν ht he hν).1
      (noncentral_inverse_estimate t e ν ht he hν).2.1 v

theorem regularizedInverseBlock_block (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (ν : Alias) (v : Polarization) :
    regularizedInverseBlock t e ν (regularizedBlock t e ν v) = v := by
  by_cases hν : IsCentralAlias ν
  · have hd := longitudinal_denominator_norm (cornerSigns ν) (scaledMomentum t) (totalEnergy e)
      (cornerSigns_norm_sq ν hν) (scaledMomentum_norm_le t ht) (totalEnergy_norm_bounds e he).1
    have hd0 : longitudinalDenominator (cornerSigns ν) (scaledMomentum t) (totalEnergy e) ≠ 0 :=
      norm_pos_iff.mp (by linarith)
    rw [regularizedBlock_central t e ν hν, regularizedInverseBlock, ite_eq_left hν]
    exact central_regularized_inverse_right_apply (cornerSigns ν) (scaledMomentum t)
      ((Real.pi : ℂ) / 2) (totalEnergy e) (cornerSigns_norm_sq ν hν) hd0 v
  · rw [regularizedBlock_noncentral t e ν hν, regularizedInverseBlock, ite_eq_right hν]
    exact inverseBlock_block _ _ (noncentral_inverse_estimate t e ν ht he hν).1
      (noncentral_inverse_estimate t e ν ht he hν).2.1 v

def regularizedFree (t : Momentum) (e : ℂ) : FiberSpace →ₗ.[ℂ] FiberSpace :=
  maximalOperator (regularizedBlock t e)

/-- Equality with the actual momentum-dependent domain is proved, not assumed. -/
theorem regularizedFree_domain (t : Momentum) (e : ℂ) :
    (regularizedFree t e).domain = (operator (scaledMomentum t) (totalEnergy e)).domain :=
  maximalDomain_eq_off_central _ _ (regularizedBlock_noncentral t e)

def regularizedFreeInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    BoundedInverse (regularizedFree t e) where
  map := boundedBlocks (regularizedInverseBlock t e) (by norm_num : (0 : ℝ) ≤ 6 / 5)
    (regularizedInverseBlock_norm_le t e ht he)
  mem_domain := boundedBlocks_mem_maximalDomain (regularizedBlock t e) (regularizedInverseBlock t e)
    (by norm_num) (regularizedInverseBlock_norm_le t e ht he) (regularizedBlock_inverse t e ht he)
  apply_map := maximalOperator_boundedBlocks (regularizedBlock t e) (regularizedInverseBlock t e)
    (by norm_num) (regularizedInverseBlock_norm_le t e ht he) (regularizedBlock_inverse t e ht he)
  map_apply := boundedBlocks_maximalOperator (regularizedBlock t e) (regularizedInverseBlock t e)
    (by norm_num) (regularizedInverseBlock_norm_le t e ht he) (regularizedInverseBlock_block t e ht he)

theorem regularizedFreeInverse_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖(regularizedFreeInverse t e ht he).map‖ ≤ 6 / 5 := by
  apply boundedBlocks_norm_le
  · norm_num
  · exact regularizedInverseBlock_norm_le t e ht he

end Maxwell.Continuum.ClusterComplement
