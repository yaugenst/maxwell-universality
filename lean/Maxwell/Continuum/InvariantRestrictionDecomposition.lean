import Maxwell.Continuum.InvariantRestriction
import Maxwell.Continuum.HighSchur
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Exact domain splitting under the ambient orthogonal unitary, and the
bounded low operator supplied by finite dimensionality. -/

noncomputable section

namespace Maxwell.Continuum.InvariantRestriction.Data

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} {K : Submodule ℂ H} [CompleteSpace K]
variable (F : InvariantRestriction.Data A K) (hA : IsSelfAdjoint A)

/-- The orthogonal unitary identifies precisely the full operator domain
with K × D(A_high). -/
theorem product_mem_domain_iff (v : HighSchur.Ambient K Kᗮ) :
    v ∈ HighSchur.domain (L := K) (F.highOperator hA) ↔ K.orthogonalDecomposition.symm v ∈ A.domain := by
  change ((v.ofLp.2 : Kᗮ) : H) ∈ A.domain ↔
    (v.ofLp.1 : H) + (v.ofLp.2 : H) ∈ A.domain
  constructor
  · exact fun h => A.domain.add_mem (F.subset_domain v.ofLp.1.property) h
  · intro h
    have hs := A.domain.sub_mem h (F.subset_domain v.ofLp.1.property)
    simpa only [add_sub_cancel_left] using hs

def domainToProduct : A.domain →ₗ[ℂ] HighSchur.domain (L := K) (F.highOperator hA) :=
  (K.orthogonalDecomposition.toLinearMap.comp A.domain.subtype).codRestrict
    (HighSchur.domain (L := K) (F.highOperator hA)) (by
      intro u
      apply (F.product_mem_domain_iff hA _).mpr
      change K.orthogonalDecomposition.symm (K.orthogonalDecomposition (u : H)) ∈ A.domain
      simpa only [LinearIsometryEquiv.symm_apply_apply] using u.property)

/-- This is the restriction of the ambient unitary, not an abstract
isomorphism chosen from a dimension count. -/
def domainEquiv : A.domain ≃ₗ[ℂ] HighSchur.domain (L := K) (F.highOperator hA) where
  __ := F.domainToProduct hA
  invFun v := ⟨K.orthogonalDecomposition.symm v, (F.product_mem_domain_iff hA v).mp v.property⟩
  left_inv u := Subtype.ext (K.orthogonalDecomposition.symm_apply_apply u)
  right_inv v := Subtype.ext (K.orthogonalDecomposition.apply_symm_apply v)

@[simp] theorem domainEquiv_coe (u : A.domain) :
    (F.domainEquiv hA u : HighSchur.Ambient K Kᗮ) = K.orthogonalDecomposition u := rfl

@[simp] theorem domainEquiv_symm_coe (v : HighSchur.domain (L := K) (F.highOperator hA)) :
    ((F.domainEquiv hA).symm v : H) = K.orthogonalDecomposition.symm v := rfl

@[simp] theorem domainEquiv_low (u : A.domain) :
    HighSchur.low (F.highOperator hA) (F.domainEquiv hA u) = K.orthogonalProjectionOnto u := by
  change (K.orthogonalDecomposition (u : H)).ofLp.1 = _
  rw [Submodule.orthogonalDecomposition_apply]

@[simp] theorem domainEquiv_high (u : A.domain) :
    HighSchur.high (F.highOperator hA) (F.domainEquiv hA u) = F.domainHighProjection u := by
  apply Subtype.ext
  change (K.orthogonalDecomposition (u : H)).ofLp.2 = _
  rw [Submodule.orthogonalDecomposition_apply]
  rfl

theorem action_decomposition (u : A.domain) :
    A u = (F.lowLinear (K.orthogonalProjectionOnto u) : H) +
      (F.highOperator hA (F.domainHighProjection u) : H) := by
  have hd : u = F.lowInclusion (K.orthogonalProjectionOnto u) +
      highInclusion A K (F.domainHighProjection u) :=
    Subtype.ext (decomposition (K := K) (u : H)).symm
  exact (congrArg A hd).trans (A.map_add _ _)

include hA in
theorem lowProjection_action (u : A.domain) :
    K.orthogonalProjectionOnto (A u) = F.lowLinear (K.orthogonalProjectionOnto u) := by
  rw [F.action_decomposition hA u, map_add,
    K.orthogonalProjectionOnto_mem_subspace_eq_self,
    K.orthogonalProjectionOnto_eq_zero_iff.mpr
      (F.highOperator hA (F.domainHighProjection u)).property, add_zero]

variable [FiniteDimensional ℂ K]

/-- The actual low action is bounded because the invariant low space is finite. -/
def lowAction : K →L[ℂ] K := F.lowLinear.toContinuousLinearMap

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem lowAction_apply (x : K) : F.lowAction x = F.lowLinear x := rfl

include hA in
omit [CompleteSpace K] in
theorem lowAction_symmetric : F.lowAction.IsSymmetric := by
  intro x y
  exact formal_of_selfAdjoint hA (F.lowInclusion x) (F.lowInclusion y)

end Maxwell.Continuum.InvariantRestriction.Data
