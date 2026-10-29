import Maxwell.Continuum.ClusterComplementEquations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of the literal fixed transverse cluster

Each of the eight central aliases contributes the two-dimensional kernel
of its rank-one longitudinal projection.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber
open scoped InnerProductSpace Classical

abbrev CentralAlias := {ν : Alias // IsCentralAlias ν}

instance : Fintype CentralAlias := centralAliases_finite.fintype

def centralAliasEquiv : CentralAlias ≃ (Fin 3 → Bool) where
  toFun ν j := if ν.val j = -1 then false else true
  invFun b := ⟨fun j => if b j then 0 else -1, by intro j; cases b j <;> simp⟩
  left_inv ν := by
    apply Subtype.ext
    funext j
    rcases ν.property j with h | h <;> simp [h]
  right_inv b := by
    funext j
    cases h : b j <;> simp [h]

theorem centralAlias_card : Fintype.card CentralAlias = 8 := by
  rw [Fintype.card_congr centralAliasEquiv]
  norm_num

theorem longitudinal_self (s : Fin 3 → ℝ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) :
    longitudinal s (momentumVector (realMomentum s)) = momentumVector (realMomentum s) := by
  rw [longitudinal_eq_rankOne]
  change (1 / 3 : ℂ) • (inner ℂ (momentumVector (realMomentum s))
    (momentumVector (realMomentum s)) • momentumVector (realMomentum s)) = _
  have hinner : inner ℂ (momentumVector (realMomentum s)) (momentumVector (realMomentum s)) =
      (3 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow, hs]
    norm_num
  rw [hinner, smul_smul]
  norm_num

theorem longitudinal_range (s : Fin 3 → ℝ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) :
    LinearMap.range (longitudinal s).toLinearMap =
      Submodule.span ℂ {momentumVector (realMomentum s)} := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    rw [ContinuousLinearMap.coe_coe, longitudinal_eq_rankOne]
    change (1 / 3 : ℂ) • (inner ℂ (momentumVector (realMomentum s)) u •
      momentumVector (realMomentum s)) ∈ _
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact ⟨momentumVector (realMomentum s), longitudinal_self s hs⟩

theorem longitudinal_ker_finrank (s : Fin 3 → ℝ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) :
    Module.finrank ℂ (LinearMap.ker (longitudinal s).toLinearMap) = 2 := by
  have hnonzero : momentumVector (realMomentum s) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs
    norm_num at hs
  have hd := (longitudinal s).toLinearMap.finrank_range_add_finrank_ker
  rw [longitudinal_range s hs, finrank_span_singleton hnonzero,
    finrank_euclideanSpace_fin] at hd
  omega

def transverseSpace (ν : CentralAlias) : Submodule ℂ Polarization :=
  LinearMap.ker (longitudinal (cornerSigns ν.val)).toLinearMap

theorem transverseSpace_finrank (ν : CentralAlias) : Module.finrank ℂ (transverseSpace ν) = 2 :=
  longitudinal_ker_finrank (cornerSigns ν.val) (cornerSigns_norm_sq ν.val ν.property)

def clusterSpace : Submodule ℂ FiberSpace := LinearMap.range clusterProjection.toLinearMap

theorem mem_clusterSpace_iff (u : FiberSpace) : u ∈ clusterSpace ↔ clusterProjection u = u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact clusterProjection_idempotent v
  · intro hu
    exact ⟨u, hu⟩

theorem clusterSpace_noncentral (u : clusterSpace) (ν : Alias) (hν : ¬IsCentralAlias ν) :
    u.val ν = 0 := by
  have h := congrArg (fun z : FiberSpace => z ν) ((mem_clusterSpace_iff u.val).mp u.property)
  simpa only [clusterProjection_apply, clusterBlock_noncentral ν hν, zero_apply] using h.symm

theorem clusterSpace_transverse (u : clusterSpace) (ν : CentralAlias) :
    u.val ν.val ∈ transverseSpace ν := by
  have h := congrArg (fun z : FiberSpace => z ν.val) ((mem_clusterSpace_iff u.val).mp u.property)
  rw [clusterProjection_apply, clusterBlock_central ν.val ν.property] at h
  change u.val ν.val - longitudinal (cornerSigns ν.val) (u.val ν.val) = u.val ν.val at h
  exact sub_eq_self.mp h

def assembleTransverse (f : ∀ ν : CentralAlias, transverseSpace ν) : FiberSpace :=
  ⟨fun ν => if hν : IsCentralAlias ν then (f ⟨ν, hν⟩).val else 0,
    central_support_memℓp _ (by intro ν hν; simp [hν])⟩

theorem assembleTransverse_central (f : ∀ ν : CentralAlias, transverseSpace ν) (ν : CentralAlias) :
    assembleTransverse f ν.val = (f ν).val := by simp [assembleTransverse, ν.property]

theorem assembleTransverse_noncentral (f : ∀ ν : CentralAlias, transverseSpace ν)
    (ν : Alias) (hν : ¬IsCentralAlias ν) : assembleTransverse f ν = 0 := by
  simp [assembleTransverse, hν]

theorem assembleTransverse_mem (f : ∀ ν : CentralAlias, transverseSpace ν) :
    assembleTransverse f ∈ clusterSpace := by
  apply (mem_clusterSpace_iff _).mpr
  apply Subtype.ext
  funext ν
  by_cases hν : IsCentralAlias ν
  · rw [clusterProjection_apply, clusterBlock_central ν hν,
      assembleTransverse_central f ⟨ν, hν⟩]
    change (f ⟨ν, hν⟩).val - longitudinal (cornerSigns ν) (f ⟨ν, hν⟩).val = (f ⟨ν, hν⟩).val
    rw [show longitudinal (cornerSigns ν) (f ⟨ν, hν⟩).val = 0 from (f ⟨ν, hν⟩).property, sub_zero]
  · rw [clusterProjection_apply, clusterBlock_noncentral ν hν, zero_apply,
      assembleTransverse_noncentral f ν hν]

def clusterPiEquiv : clusterSpace ≃ₗ[ℂ] (∀ ν : CentralAlias, transverseSpace ν) where
  toFun u ν := ⟨u.val ν.val, clusterSpace_transverse u ν⟩
  invFun f := ⟨assembleTransverse f, assembleTransverse_mem f⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    funext ν
    by_cases hν : IsCentralAlias ν
    · simp [assembleTransverse, hν]
    · rw [assembleTransverse_noncentral _ ν hν, clusterSpace_noncentral u ν hν]
  right_inv f := by
    funext ν
    apply Subtype.ext
    exact assembleTransverse_central f ν
  map_add' u v := by ext ν; rfl
  map_smul' c u := by ext ν; rfl

theorem clusterSpace_finrank : Module.finrank ℂ clusterSpace = 16 := by
  rw [clusterPiEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp only [transverseSpace_finrank, Finset.sum_const, Finset.card_univ,
    centralAlias_card, smul_eq_mul]

end Maxwell.Continuum.ClusterComplement
