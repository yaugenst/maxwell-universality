import Maxwell.Continuum.ClusterComplementProjection
import Maxwell.Continuum.CalibrationNeumann

/-! The calibration split retains all 24 components at the eight
central aliases. Its infinite complement is the literal free Maxwell
multiplier, with the actual maximal domain and explicit block inverse. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open FreeFiber SelfAdjointResolvent
open scoped Classical

def centralAliasBlock (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then 1 else 0

def noncentralAliasBlock (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then 0 else 1

theorem centralAliasBlock_projection (ν : Alias) : IsStarProjection (centralAliasBlock ν) := by
  unfold centralAliasBlock
  split_ifs
  · exact .one _
  · exact .zero _

theorem centralAliasBlock_norm (ν : Alias) : ‖centralAliasBlock ν‖ ≤ 1 :=
  IsStarProjection.norm_le _ (centralAliasBlock_projection ν)

def centralAliasProjection : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks centralAliasBlock zero_le_one centralAliasBlock_norm

def noncentralAliasProjection : FiberSpace →L[ℂ] FiberSpace := 1-centralAliasProjection

theorem centralAliasProjection_apply (u : FiberSpace) (ν : Alias) :
    centralAliasProjection u ν = if IsCentralAlias ν then u ν else 0 := by
  change centralAliasBlock ν (u ν) = _
  unfold centralAliasBlock
  split_ifs <;> rfl

theorem noncentralAliasProjection_apply (u : FiberSpace) (ν : Alias) :
    noncentralAliasProjection u ν = if IsCentralAlias ν then 0 else u ν := by
  change u ν-centralAliasProjection u ν = _
  rw [centralAliasProjection_apply]
  split_ifs <;> simp

theorem centralAliasProjection_projection : IsStarProjection centralAliasProjection := by
  refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    funext ν
    change centralAliasProjection (centralAliasProjection u) ν = centralAliasProjection u ν
    simp only [centralAliasProjection_apply]
    split_ifs <;> rfl
  · intro u v
    change inner ℂ (centralAliasProjection u) v = inner ℂ u (centralAliasProjection v)
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro ν
    rw [centralAliasProjection_apply, centralAliasProjection_apply]
    split_ifs <;> simp

theorem noncentralAliasProjection_norm : ‖noncentralAliasProjection‖ ≤ 1 :=
  IsStarProjection.norm_le _ centralAliasProjection_projection.one_sub

def calibrationFreeBlock (t : Momentum) (e : ℂ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then 1 else block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e)

def calibrationInverseBlock (t : Momentum) (e : ℂ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then 1 else inverseBlock (aliasMomentum (scaledMomentum t) ν) (totalEnergy e)

theorem calibrationFreeBlock_compression (t : Momentum) (e : ℂ) (ν : Alias) :
    calibrationFreeBlock t e ν = noncentralAliasBlock ν *
      block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e) * noncentralAliasBlock ν +
      centralAliasBlock ν := by
  unfold calibrationFreeBlock noncentralAliasBlock centralAliasBlock
  split_ifs <;> simp

theorem calibrationInverseBlock_norm (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (ν : Alias) :
    ‖calibrationInverseBlock t e ν‖ ≤ 1 := by
  by_cases hν : IsCentralAlias ν
  · rw [calibrationInverseBlock, ite_eq_left hν]
    exact ContinuousLinearMap.norm_id_le
  · rw [calibrationInverseBlock, ite_eq_right hν]
    exact (noncentral_inverse_estimate t e ν ht he hν).2.2.trans (by norm_num)

theorem calibrationBlock_inverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (ν : Alias) (u : Polarization) :
    calibrationFreeBlock t e ν (calibrationInverseBlock t e ν u) = u := by
  by_cases hν : IsCentralAlias ν
  · simp only [calibrationFreeBlock, calibrationInverseBlock, hν, ↓reduceIte]
    rfl
  · simp only [calibrationFreeBlock, calibrationInverseBlock, hν, ↓reduceIte]
    exact block_inverseBlock _ _ (noncentral_inverse_estimate t e ν ht he hν).1
      (noncentral_inverse_estimate t e ν ht he hν).2.1 u

theorem calibrationInverse_block (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (ν : Alias) (u : Polarization) :
    calibrationInverseBlock t e ν (calibrationFreeBlock t e ν u) = u := by
  by_cases hν : IsCentralAlias ν
  · simp only [calibrationFreeBlock, calibrationInverseBlock, hν, ↓reduceIte]
    rfl
  · simp only [calibrationFreeBlock, calibrationInverseBlock, hν, ↓reduceIte]
    exact inverseBlock_block _ _ (noncentral_inverse_estimate t e ν ht he hν).1
      (noncentral_inverse_estimate t e ν ht he hν).2.1 u

def calibrationFree (t : Momentum) (e : ℂ) : FiberSpace →ₗ.[ℂ] FiberSpace :=
  maximalOperator (calibrationFreeBlock t e)

theorem calibrationFree_domain (t : Momentum) (e : ℂ) :
    (calibrationFree t e).domain = (operator (scaledMomentum t) (totalEnergy e)).domain := by
  apply ClusterComplement.maximalDomain_eq_off_central
  intro ν hν
  simp only [calibrationFreeBlock, hν, ↓reduceIte]

def calibrationFreeInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) :
    BoundedInverse (calibrationFree t e) where
  map := boundedBlocks (calibrationInverseBlock t e) zero_le_one (calibrationInverseBlock_norm t e ht he)
  mem_domain := boundedBlocks_mem_maximalDomain _ _ zero_le_one
    (calibrationInverseBlock_norm t e ht he) (calibrationBlock_inverse t e ht he)
  apply_map := maximalOperator_boundedBlocks _ _ zero_le_one
    (calibrationInverseBlock_norm t e ht he) (calibrationBlock_inverse t e ht he)
  map_apply := boundedBlocks_maximalOperator _ _ zero_le_one
    (calibrationInverseBlock_norm t e ht he) (calibrationInverse_block t e ht he)

theorem calibrationFreeInverse_norm (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖(calibrationFreeInverse t e ht he).map‖ ≤ 1 :=
  boundedBlocks_norm_le _ zero_le_one (calibrationInverseBlock_norm t e ht he)

#print axioms calibrationFree_domain
#print axioms calibrationFreeInverse

end Maxwell.Continuum.Calibration
