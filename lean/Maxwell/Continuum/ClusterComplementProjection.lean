import Maxwell.Continuum.ClusterComplementCentralNorm
import Mathlib.Data.Fintype.Pi

/-!
# Literal fixed cluster projection on the infinite alias Hilbert space

The cluster contains exactly the transverse fields at the eight central
aliases. Its complement retains the central longitudinal fields and all
three components at every noncentral alias.
-/

noncomputable section

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber
open scoped InnerProductSpace Classical

theorem centralAliases_finite : Set.Finite {ν : Alias | IsCentralAlias ν} := by
  simpa only [IsCentralAlias, Set.mem_insert_iff, Set.mem_singleton_iff] using
    Set.Finite.pi' (fun _ : Fin 3 => Set.toFinite ({-1, 0} : Set ℤ))

theorem central_support_memℓp (f : Alias → Polarization)
    (hf : ∀ ν, ¬IsCentralAlias ν → f ν = 0) : Memℓp f 2 := by
  apply (memℓp_zero (E := fun _ : Alias => Polarization) ?_).of_exponent_ge (by norm_num)
  apply centralAliases_finite.subset
  intro ν hν
  by_contra h
  exact hν (hf ν h)

/-- Changing finitely many blocks preserves the actual maximal domain, even
when their entries and the domain depend on complex momentum. -/
theorem maximalDomain_eq_off_central (B C : Alias → Polarization →L[ℂ] Polarization)
    (hBC : ∀ ν, ¬IsCentralAlias ν → B ν = C ν) : maximalDomain B = maximalDomain C := by
  have hdiff (u : FiberSpace) : Memℓp (fun ν => B ν (u ν) - C ν (u ν)) 2 := by
    apply central_support_memℓp
    intro ν hν
    rw [hBC ν hν, sub_self]
  ext u
  change Memℓp (fun ν => B ν (u ν)) 2 ↔ Memℓp (fun ν => C ν (u ν)) 2
  constructor
  · intro hu
    convert hu.sub (hdiff u) using 1
    funext ν
    simp only [Pi.sub_apply, sub_sub_cancel]
  · intro hu
    convert (hdiff u).add hu using 1
    funext ν
    simp only [Pi.add_apply, sub_add_cancel]

def clusterBlock (ν : Alias) : Polarization →L[ℂ] Polarization :=
  if IsCentralAlias ν then 1 - longitudinal (cornerSigns ν) else 0

def complementBlock (ν : Alias) : Polarization →L[ℂ] Polarization := 1 - clusterBlock ν

theorem clusterBlock_central (ν : Alias) (hν : IsCentralAlias ν) :
    clusterBlock ν = 1 - longitudinal (cornerSigns ν) := by simp [clusterBlock, hν]

theorem clusterBlock_noncentral (ν : Alias) (hν : ¬IsCentralAlias ν) :
    clusterBlock ν = 0 := by simp [clusterBlock, hν]

theorem complementBlock_central (ν : Alias) (hν : IsCentralAlias ν) :
    complementBlock ν = longitudinal (cornerSigns ν) := by
  rw [complementBlock, clusterBlock_central ν hν, sub_sub_cancel]

theorem complementBlock_noncentral (ν : Alias) (hν : ¬IsCentralAlias ν) :
    complementBlock ν = 1 := by rw [complementBlock, clusterBlock_noncentral ν hν, sub_zero]

theorem clusterBlock_isStarProjection (ν : Alias) : IsStarProjection (clusterBlock ν) := by
  by_cases hν : IsCentralAlias ν
  · rw [clusterBlock_central ν hν]
    exact (longitudinal_isStarProjection _ (cornerSigns_norm_sq ν hν)).one_sub
  · rw [clusterBlock_noncentral ν hν]
    exact .zero _

theorem complementBlock_isStarProjection (ν : Alias) : IsStarProjection (complementBlock ν) :=
  (clusterBlock_isStarProjection ν).one_sub

theorem clusterBlock_norm_le (ν : Alias) : ‖clusterBlock ν‖ ≤ 1 :=
  IsStarProjection.norm_le _ (clusterBlock_isStarProjection ν)

theorem complementBlock_norm_le (ν : Alias) : ‖complementBlock ν‖ ≤ 1 :=
  IsStarProjection.norm_le _ (complementBlock_isStarProjection ν)

def clusterProjection : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks clusterBlock (by norm_num : (0 : ℝ) ≤ 1) clusterBlock_norm_le

def complementProjection : FiberSpace →L[ℂ] FiberSpace := 1 - clusterProjection

@[simp]
theorem clusterProjection_apply (u : FiberSpace) (ν : Alias) :
    clusterProjection u ν = clusterBlock ν (u ν) := rfl

@[simp]
theorem complementProjection_apply (u : FiberSpace) (ν : Alias) :
    complementProjection u ν = complementBlock ν (u ν) := rfl

theorem clusterProjection_isStarProjection : IsStarProjection clusterProjection := by
  refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    funext ν
    exact congrArg (fun T : Polarization →L[ℂ] Polarization => T (u ν))
      (clusterBlock_isStarProjection ν).isIdempotentElem.eq
  · intro u v
    change inner ℂ (clusterProjection u) v = inner ℂ u (clusterProjection v)
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro ν
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (clusterBlock_isStarProjection ν).isSelfAdjoint) (u ν) (v ν)

theorem complementProjection_isStarProjection : IsStarProjection complementProjection :=
  clusterProjection_isStarProjection.one_sub

theorem clusterProjection_norm_le : ‖clusterProjection‖ ≤ 1 :=
  IsStarProjection.norm_le _ clusterProjection_isStarProjection

theorem complementProjection_norm_le : ‖complementProjection‖ ≤ 1 :=
  IsStarProjection.norm_le _ complementProjection_isStarProjection

theorem clusterProjection_mem_domain (q : Momentum) (E : ℂ) (u : FiberSpace) :
    clusterProjection u ∈ (operator q E).domain := by
  apply central_support_memℓp
  intro ν hν
  simp only [clusterProjection_apply, clusterBlock_noncentral ν hν, zero_apply, map_zero]

theorem complementProjection_mem_domain (q : Momentum) (E : ℂ)
    (u : (operator q E).domain) : complementProjection u.val ∈ (operator q E).domain :=
  (operator q E).domain.sub_mem u.property (clusterProjection_mem_domain q E u.val)

end Maxwell.Continuum.ClusterComplement
