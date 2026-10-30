import Maxwell.Continuum.CalibrationAliasSupport
import Maxwell.Continuum.ClusterComplementDimension

/-! The calibration central space consists of all three polarizations
at each of the eight central aliases. Its dimension is exactly 24. -/

noncomputable section

set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber
open scoped Classical

@[simp] theorem centralAliasProjection_idempotent (u : FiberSpace) :
    centralAliasProjection (centralAliasProjection u) = centralAliasProjection u :=
  congrArg (fun T : FiberSpace →L[ℂ] FiberSpace => T u)
    centralAliasProjection_projection.isIdempotentElem.eq

@[simp] theorem centralAliasProjection_noncentral (u : FiberSpace) :
    centralAliasProjection (noncentralAliasProjection u) = 0 := by
  change centralAliasProjection (u-centralAliasProjection u) = 0
  rw [map_sub, centralAliasProjection_idempotent, sub_self]

@[simp] theorem noncentralAliasProjection_central (u : FiberSpace) :
    noncentralAliasProjection (centralAliasProjection u) = 0 := by
  change centralAliasProjection u-centralAliasProjection (centralAliasProjection u) = 0
  rw [centralAliasProjection_idempotent, sub_self]

@[simp] theorem noncentralAliasProjection_idempotent (u : FiberSpace) :
    noncentralAliasProjection (noncentralAliasProjection u) = noncentralAliasProjection u :=
  congrArg (fun T : FiberSpace →L[ℂ] FiberSpace => T u)
    centralAliasProjection_projection.one_sub.isIdempotentElem.eq

theorem centralAliasProjection_norm : ‖centralAliasProjection‖ ≤ 1 :=
  IsStarProjection.norm_le _ centralAliasProjection_projection

def centralSpace : Submodule ℂ FiberSpace := LinearMap.range centralAliasProjection.toLinearMap

theorem mem_centralSpace_iff (u : FiberSpace) :
    u ∈ centralSpace ↔ centralAliasProjection u = u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact centralAliasProjection_idempotent v
  · intro hu
    exact ⟨u, hu⟩

theorem centralSpace_noncentral (u : centralSpace) (ν : Alias) (hν : ¬IsCentralAlias ν) :
    u.val ν = 0 := by
  have h := congrArg (fun z : FiberSpace => z ν) ((mem_centralSpace_iff u.val).mp u.property)
  simpa only [centralAliasProjection_apply, hν, ↓reduceIte] using h.symm

def assembleCentral (f : ClusterComplement.CentralAlias → Polarization) : FiberSpace :=
  ⟨fun ν => if hν : IsCentralAlias ν then f ⟨ν,hν⟩ else 0,
    ClusterComplement.central_support_memℓp _ (by intro ν hν; simp [hν])⟩

theorem assembleCentral_mem (f : ClusterComplement.CentralAlias → Polarization) :
    assembleCentral f ∈ centralSpace := by
  apply (mem_centralSpace_iff _).mpr
  apply Subtype.ext
  funext ν
  rw [centralAliasProjection_apply]
  by_cases hν : IsCentralAlias ν <;> simp [assembleCentral, hν]

def centralPiEquiv : centralSpace ≃ₗ[ℂ] (ClusterComplement.CentralAlias → Polarization) where
  toFun u ν := u.val ν.val
  invFun f := ⟨assembleCentral f, assembleCentral_mem f⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    funext ν
    by_cases hν : IsCentralAlias ν
    · simp [assembleCentral, hν]
    · simp [assembleCentral, hν, centralSpace_noncentral u ν hν]
  right_inv f := by funext ν; simp [assembleCentral, ν.property]
  map_add' u v := by ext ν; rfl
  map_smul' c u := by ext ν; rfl

theorem centralSpace_finrank : Module.finrank ℂ centralSpace = 24 := by
  rw [centralPiEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp only [finrank_euclideanSpace_fin, Finset.sum_const, Finset.card_univ,
    ClusterComplement.centralAlias_card, smul_eq_mul]

instance : FiniteDimensional ℂ centralSpace :=
  FiniteDimensional.of_finrank_pos (by rw [centralSpace_finrank]; norm_num)

theorem centralAliasProjection_mem_domain (q : Momentum) (E : ℂ) (u : FiberSpace) :
    centralAliasProjection u ∈ (operator q E).domain := by
  apply ClusterComplement.central_support_memℓp
  intro ν hν
  rw [centralAliasProjection_apply]
  simp only [hν, ↓reduceIte, map_zero]

theorem noncentralAliasProjection_mem_domain (q : Momentum) (E : ℂ)
    (u : (operator q E).domain) : noncentralAliasProjection u.val ∈ (operator q E).domain :=
  (operator q E).domain.sub_mem u.property (centralAliasProjection_mem_domain q E u.val)

def centralFreeBound (t : Momentum) (e : ℂ) : ℝ :=
  ∑ ν : ClusterComplement.CentralAlias,
    ‖block (aliasMomentum (scaledMomentum t) ν.val) (totalEnergy e)‖

def centralFreeBlock (t : Momentum) (e : ℂ) (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e) else 0

theorem centralFreeBound_nonneg (t : Momentum) (e : ℂ) : 0 ≤ centralFreeBound t e :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem centralFreeBlock_norm (t : Momentum) (e : ℂ) (ν : Alias) :
    ‖centralFreeBlock t e ν‖ ≤ centralFreeBound t e := by
  by_cases hν : IsCentralAlias ν
  · simp only [centralFreeBlock, hν, ↓reduceIte]
    change ‖block (aliasMomentum (scaledMomentum t) (⟨ν,hν⟩ :
      ClusterComplement.CentralAlias).val) (totalEnergy e)‖ ≤
      ∑ μ : ClusterComplement.CentralAlias,
        ‖block (aliasMomentum (scaledMomentum t) μ.val) (totalEnergy e)‖
    exact Finset.single_le_sum (f := fun μ : ClusterComplement.CentralAlias =>
      ‖block (aliasMomentum (scaledMomentum t) μ.val) (totalEnergy e)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  · simp only [centralFreeBlock, hν, ↓reduceIte, norm_zero]
    exact centralFreeBound_nonneg t e

def centralFree (t : Momentum) (e : ℂ) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (centralFreeBlock t e) (centralFreeBound_nonneg t e) (centralFreeBlock_norm t e)

theorem centralFree_apply (t : Momentum) (e : ℂ) (u : FiberSpace) :
    centralFree t e u = operator (scaledMomentum t) (totalEnergy e)
      ⟨centralAliasProjection u, centralAliasProjection_mem_domain _ _ u⟩ := by
  apply Subtype.ext
  funext ν
  change centralFreeBlock t e ν (u ν) =
    block (aliasMomentum (scaledMomentum t) ν) (totalEnergy e) (centralAliasProjection u ν)
  rw [centralAliasProjection_apply]
  unfold centralFreeBlock
  split_ifs <;> simp

theorem centralFree_projection (t : Momentum) (e : ℂ) (u : FiberSpace) :
    centralAliasProjection (centralFree t e u) = centralFree t e u := by
  apply Subtype.ext
  funext ν
  rw [centralAliasProjection_apply]
  change (if IsCentralAlias ν then centralFreeBlock t e ν (u ν) else 0) =
    centralFreeBlock t e ν (u ν)
  by_cases hν : IsCentralAlias ν <;> simp [centralFreeBlock, hν]

theorem centralFree_central (t : Momentum) (e : ℂ) (u : FiberSpace) :
    centralFree t e (centralAliasProjection u) = centralFree t e u := by
  rw [centralFree_apply, centralFree_apply]
  congr 1
  exact Subtype.ext (centralAliasProjection_idempotent u)

def restrictCentral (A : FiberSpace →L[ℂ] FiberSpace)
    (hA : ∀ u, centralAliasProjection (A u) = A u) : centralSpace →L[ℂ] centralSpace :=
  (A.codRestrict centralSpace (fun u => (mem_centralSpace_iff _).mpr (hA u))).comp centralSpace.subtypeL

theorem restrictCentral_norm (A : FiberSpace →L[ℂ] FiberSpace)
    (hA : ∀ u, centralAliasProjection (A u) = A u) : ‖restrictCentral A hA‖ ≤ ‖A‖ := by
  apply (restrictCentral A hA).opNorm_le_bound (norm_nonneg A)
  intro u
  exact A.le_opNorm u.val

#print axioms centralSpace_finrank
#print axioms centralFree_apply

end Maxwell.Continuum.Calibration
