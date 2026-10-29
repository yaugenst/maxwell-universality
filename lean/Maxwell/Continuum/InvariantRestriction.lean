import Maxwell.Continuum.FormPerturbation
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# A self-adjoint operator restricted to the orthogonal high space

A closed low subspace contained in D(A), invariant under A, reduces the
actual self-adjoint operator. The high restriction uses exactly the induced
domain; its density and self-adjointness are proved rather than assumed.
-/

noncomputable section

namespace Maxwell.Continuum.InvariantRestriction

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The low subspace consists of actual domain vectors and is invariant. -/
structure Data (A : H →ₗ.[ℂ] H) (K : Submodule ℂ H) : Prop where
  subset_domain : K ≤ A.domain
  map_mem : ∀ x : K, A ⟨(x : H), subset_domain x.property⟩ ∈ K

namespace Data

variable {A : H →ₗ.[ℂ] H} {K : Submodule ℂ H} (F : Data A K)

def lowInclusion : K →ₗ[ℂ] A.domain := Submodule.inclusion F.subset_domain

def lowLinear : K →ₗ[ℂ] K :=
  (A.toFun.comp F.lowInclusion).codRestrict K F.map_mem

def highDomain (A : H →ₗ.[ℂ] H) (K : Submodule ℂ H) : Submodule ℂ Kᗮ :=
  A.domain.comap Kᗮ.subtype

def highInclusion (A : H →ₗ.[ℂ] H) (K : Submodule ℂ H) :
    highDomain A K →ₗ[ℂ] A.domain where
  toFun u := ⟨u.val.val, u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formal_of_selfAdjoint (hA : IsSelfAdjoint A) : A.IsFormalAdjoint A := by
  simpa only [LinearPMap.isSelfAdjoint_def.mp hA] using
    LinearPMap.adjoint_isFormalAdjoint hA.dense_domain

include F in
theorem highAction_mem (hA : IsSelfAdjoint A) (u : highDomain A K) :
    A (highInclusion A K u) ∈ Kᗮ := by
  apply (K.mem_orthogonal _).mpr
  intro x hx
  have hs := formal_of_selfAdjoint hA (F.lowInclusion ⟨x, hx⟩) (highInclusion A K u)
  have ho := (K.mem_orthogonal _).mp u.val.property
    (A (F.lowInclusion ⟨x, hx⟩)) (F.map_mem ⟨x, hx⟩)
  exact hs.symm.trans ho

/-- The literal restriction to Kᗮ, with domain D(A)∩Kᗮ. -/
def highOperator (hA : IsSelfAdjoint A) : Kᗮ →ₗ.[ℂ] Kᗮ where
  domain := highDomain A K
  toFun := (A.toFun.comp (highInclusion A K)).codRestrict Kᗮ (F.highAction_mem hA)

@[simp] theorem highOperator_coe (hA : IsSelfAdjoint A) (u : highDomain A K) :
    (F.highOperator hA u : H) = A (highInclusion A K u) := rfl

variable [CompleteSpace K]

omit [CompleteSpace H] in
theorem decomposition (x : H) :
    (K.orthogonalProjectionOnto x : H) + (Kᗮ.orthogonalProjectionOnto x : H) = x :=
  K.starProjection_add_starProjection_orthogonal x

omit [CompleteSpace H] in
theorem highProjection_eq_sub (x : H) :
    (Kᗮ.orthogonalProjectionOnto x : H) = x - (K.orthogonalProjectionOnto x : H) := by
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact decomposition x

include F in
omit [CompleteSpace H] in
theorem highProjection_mem_domain (u : A.domain) :
    (Kᗮ.orthogonalProjectionOnto u : H) ∈ A.domain := by
  rw [highProjection_eq_sub]
  exact A.domain.sub_mem u.property (F.subset_domain (K.orthogonalProjectionOnto u).property)

include F in
omit [CompleteSpace H] in
theorem mem_domain_iff_highProjection (x : H) :
    x ∈ A.domain ↔ (Kᗮ.orthogonalProjectionOnto x : H) ∈ A.domain := by
  constructor
  · exact fun hx => F.highProjection_mem_domain ⟨x, hx⟩
  · intro hx
    exact decomposition (K := K) x ▸ A.domain.add_mem
      (F.subset_domain (K.orthogonalProjectionOnto x).property) hx

def domainHighProjection : A.domain →ₗ[ℂ] highDomain A K where
  toFun u := ⟨Kᗮ.orthogonalProjectionOnto u, F.highProjection_mem_domain u⟩
  map_add' u v := Subtype.ext (Kᗮ.orthogonalProjectionOnto.map_add u.val v.val)
  map_smul' c u := Subtype.ext (Kᗮ.orthogonalProjectionOnto.map_smul c u.val)

theorem highProjection_action (hA : IsSelfAdjoint A) (u : A.domain) :
    F.highOperator hA (F.domainHighProjection u) = Kᗮ.orthogonalProjectionOnto (A u) := by
  let g := F.lowInclusion (K.orthogonalProjectionOnto u)
  have hd : highInclusion A K (F.domainHighProjection u) = u - g :=
    Subtype.ext (highProjection_eq_sub (u : H))
  have hz : Kᗮ.orthogonalProjectionOnto (A g) = 0 :=
    Kᗮ.orthogonalProjectionOnto_eq_zero_iff.mpr
      (K.le_orthogonal_orthogonal (F.map_mem (K.orthogonalProjectionOnto u)))
  have hself := Kᗮ.orthogonalProjectionOnto_mem_subspace_eq_self
    (F.highOperator hA (F.domainHighProjection u))
  rw [highOperator_coe, hd, A.map_sub, map_sub, hz, sub_zero] at hself
  exact hself.symm

theorem high_dense (hA : IsSelfAdjoint A) :
    Dense ((F.highOperator hA).domain : Set Kᗮ) := by
  have hsurj : Function.Surjective Kᗮ.orthogonalProjectionOnto := by
    intro x
    exact ⟨x.val, Kᗮ.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  exact hsurj.denseRange.dense_of_mapsTo Kᗮ.orthogonalProjectionOnto.continuous
    hA.dense_domain (fun u hu => F.highProjection_mem_domain ⟨u, hu⟩)

omit [CompleteSpace K] in
theorem high_symmetric (hA : IsSelfAdjoint A) :
    (F.highOperator hA).IsFormalAdjoint (F.highOperator hA) := by
  intro u v
  exact formal_of_selfAdjoint hA (highInclusion A K u) (highInclusion A K v)

theorem high_adjoint_test (hA : IsSelfAdjoint A)
    (y : (F.highOperator hA).adjoint.domain) (u : A.domain) :
    inner ℂ ((F.highOperator hA).adjoint y : H) (u : H) =
      inner ℂ ((y : Kᗮ) : H) (A u) := by
  have h := LinearPMap.adjoint_isFormalAdjoint (F.high_dense hA) y (F.domainHighProjection u)
  change inner ℂ ((F.highOperator hA).adjoint y) (Kᗮ.orthogonalProjectionOnto u) =
    inner ℂ (y : Kᗮ) (F.highOperator hA (F.domainHighProjection u)) at h
  calc
    _ = inner ℂ ((F.highOperator hA).adjoint y) (Kᗮ.orthogonalProjectionOnto u) :=
      (Kᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left _ _).symm
    _ = inner ℂ (y : Kᗮ) (Kᗮ.orthogonalProjectionOnto (A u)) :=
      h.trans (congrArg (fun z => inner ℂ (y : Kᗮ) z) (F.highProjection_action hA u))
    _ = _ := Kᗮ.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

/-- Self-adjointness of the induced high-domain operator is a conclusion. -/
theorem high_selfAdjoint (hA : IsSelfAdjoint A) : IsSelfAdjoint (F.highOperator hA) := by
  have hmem (y : (F.highOperator hA).adjoint.domain) :
      (y : Kᗮ) ∈ (F.highOperator hA).domain := by
    have hm : ((y : Kᗮ) : H) ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _
        ⟨((F.highOperator hA).adjoint y : H), F.high_adjoint_test hA y⟩
    change ((y : Kᗮ) : H) ∈ A.domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hA] at hm
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨fun y hy => hmem ⟨y, hy⟩, ?_⟩
    intro y x hxy
    apply Subtype.ext
    have ht : A (highInclusion A K x) = ((F.highOperator hA).adjoint y : H) := by
      apply hA.dense_domain.eq_of_inner_left ℂ
      intro v hv
      have hs := formal_of_selfAdjoint hA (highInclusion A K x) ⟨v, hv⟩
      have he := F.high_adjoint_test hA y ⟨v, hv⟩
      change inner ℂ (A (highInclusion A K x)) v =
        inner ℂ ((x : Kᗮ) : H) (A ⟨v, hv⟩) at hs
      exact hs.trans (he.trans (congrArg (fun z : Kᗮ => inner ℂ (z : H) (A ⟨v, hv⟩)) hxy)).symm
    exact ht.symm
  · exact (F.high_symmetric hA).le_adjoint (F.high_dense hA)

theorem high_closed (hA : IsSelfAdjoint A) : (F.highOperator hA).IsClosed :=
  (F.high_selfAdjoint hA).isClosed

end Data
end Maxwell.Continuum.InvariantRestriction
