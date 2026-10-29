import Maxwell.Continuum.PECKernel

/-! The curl-curl domain splits exactly into kernel and transverse parts. -/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace

def gradientProjection (Ω : Opens Space) : testL2Closure Ω →L[ℂ] gradientSpace Ω :=
  (gradientSpace Ω).orthogonalProjectionOnto

def transverseProjection (Ω : Opens Space) : testL2Closure Ω →L[ℂ] transverseSpace Ω :=
  (transverseSpace Ω).orthogonalProjectionOnto

theorem kernel_decomposition (Ω : Opens Space) (u : testL2Closure Ω) :
    (gradientProjection Ω u : testL2Closure Ω) + (transverseProjection Ω u : testL2Closure Ω) = u :=
  (gradientSpace Ω).starProjection_add_starProjection_orthogonal u

theorem transverseProjection_eq_sub (Ω : Opens Space) (u : testL2Closure Ω) :
    (transverseProjection Ω u : testL2Closure Ω) = u - (gradientProjection Ω u : testL2Closure Ω) := by
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact kernel_decomposition Ω u

theorem pecCurlCurl_mem_transverse (Ω : Opens Space) (u : (pecCurlCurl Ω).domain) :
    pecCurlCurl Ω u ∈ transverseSpace Ω := by
  apply (gradientSpace Ω).mem_orthogonal _ |>.mpr
  intro g hg
  let gd : (pecCurlCurl Ω).domain := ⟨g, (pecCurlCurl Ω).ker_le_domain hg⟩
  have hz : pecCurlCurl Ω gd = 0 := (pecCurlCurl Ω).coe_mem_ker_iff.mp hg
  have hs := (pecFormEmbedding Ω).operator_symmetric gd u
  change inner ℂ (pecCurlCurl Ω gd) (u : testL2Closure Ω) =
    inner ℂ g (pecCurlCurl Ω u) at hs
  rw [hz, inner_zero_left] at hs
  exact hs.symm

@[simp] theorem gradientProjection_curlCurl (Ω : Opens Space) (u : (pecCurlCurl Ω).domain) :
    gradientProjection Ω (pecCurlCurl Ω u) = 0 :=
  (gradientSpace Ω).orthogonalProjectionOnto_eq_zero_iff.mpr (pecCurlCurl_mem_transverse Ω u)

theorem transverseProjection_mem_domain (Ω : Opens Space) (u : (pecCurlCurl Ω).domain) :
    (transverseProjection Ω u : testL2Closure Ω) ∈ (pecCurlCurl Ω).domain := by
  rw [transverseProjection_eq_sub]
  exact (pecCurlCurl Ω).domain.sub_mem u.property
    (gradient_mem_domain Ω (gradientProjection Ω u))

def transverseDomain (Ω : Opens Space) : Submodule ℂ (transverseSpace Ω) :=
  (pecCurlCurl Ω).domain.comap (transverseSpace Ω).subtype

def transverseDomainInclusion (Ω : Opens Space) :
    transverseDomain Ω →ₗ[ℂ] (pecCurlCurl Ω).domain where
  toFun u := ⟨u.val.val, u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to the literal orthogonal complement, with its full induced domain. -/
def transverseCurlCurl (Ω : Opens Space) : transverseSpace Ω →ₗ.[ℂ] transverseSpace Ω where
  domain := transverseDomain Ω
  toFun := ((pecCurlCurl Ω).toFun.comp (transverseDomainInclusion Ω)).codRestrict
    (transverseSpace Ω) fun u => pecCurlCurl_mem_transverse Ω (transverseDomainInclusion Ω u)

@[simp] theorem transverseCurlCurl_coe (Ω : Opens Space) (u : (transverseCurlCurl Ω).domain) :
    (transverseCurlCurl Ω u : testL2Closure Ω) = pecCurlCurl Ω (transverseDomainInclusion Ω u) := rfl

def domainTransverseProjection (Ω : Opens Space) :
    (pecCurlCurl Ω).domain →ₗ[ℂ] (transverseCurlCurl Ω).domain where
  toFun u := ⟨transverseProjection Ω u, transverseProjection_mem_domain Ω u⟩
  map_add' u v := Subtype.ext ((transverseProjection Ω).map_add u.val v.val)
  map_smul' r u := Subtype.ext ((transverseProjection Ω).map_smul r u.val)

theorem transverseCurlCurl_projection (Ω : Opens Space) (u : (pecCurlCurl Ω).domain) :
    (transverseCurlCurl Ω (domainTransverseProjection Ω u) : testL2Closure Ω) = pecCurlCurl Ω u := by
  let g : (pecCurlCurl Ω).domain :=
    ⟨gradientProjection Ω u, gradient_mem_domain Ω (gradientProjection Ω u)⟩
  have he : transverseDomainInclusion Ω (domainTransverseProjection Ω u) = u - g :=
    Subtype.ext (transverseProjection_eq_sub Ω u)
  rw [transverseCurlCurl_coe, he]
  change (pecCurlCurl Ω).toFun (u - g) = _
  rw [map_sub]
  have hg : pecCurlCurl Ω g = 0 := pecCurlCurl_gradient Ω (gradientProjection Ω u)
  change pecCurlCurl Ω u - pecCurlCurl Ω g = pecCurlCurl Ω u
  rw [hg, sub_zero]

theorem transverseCurlCurl_nonnegative (Ω : Opens Space) (u : (transverseCurlCurl Ω).domain) :
    0 ≤ (inner ℂ (transverseCurlCurl Ω u) (u : transverseSpace Ω)).re :=
  pecCurlCurl_nonnegative Ω (transverseDomainInclusion Ω u)

theorem transverseProjection_surjective (Ω : Opens Space) :
    Function.Surjective (transverseProjection Ω) := by
  intro x
  refine ⟨x.val, ?_⟩
  exact (transverseSpace Ω).orthogonalProjectionOnto_mem_subspace_eq_self x

theorem transverseCurlCurl_dense (Ω : Opens Space) :
    Dense ((transverseCurlCurl Ω).domain : Set (transverseSpace Ω)) :=
  (transverseProjection_surjective Ω).denseRange.dense_of_mapsTo
    (transverseProjection Ω).continuous (pecCurlCurl_dense Ω)
    (fun u hu => transverseProjection_mem_domain Ω ⟨u, hu⟩)

theorem transverseCurlCurl_symmetric (Ω : Opens Space) :
    (transverseCurlCurl Ω).IsFormalAdjoint (transverseCurlCurl Ω) := by
  intro u v
  exact (pecFormEmbedding Ω).operator_symmetric
    (transverseDomainInclusion Ω u) (transverseDomainInclusion Ω v)

theorem transverse_adjoint_test (Ω : Opens Space)
    (y : (transverseCurlCurl Ω).adjoint.domain) (u : (pecCurlCurl Ω).domain) :
    inner ℂ ((transverseCurlCurl Ω).adjoint y : testL2Closure Ω) (u : testL2Closure Ω) =
      inner ℂ ((y : transverseSpace Ω) : testL2Closure Ω) (pecCurlCurl Ω u) := by
  have h := LinearPMap.adjoint_isFormalAdjoint (transverseCurlCurl_dense Ω)
    y (domainTransverseProjection Ω u)
  change inner ℂ ((transverseCurlCurl Ω).adjoint y)
      ((transverseSpace Ω).orthogonalProjectionOnto u) =
    inner ℂ (y : transverseSpace Ω) (transverseCurlCurl Ω (domainTransverseProjection Ω u)) at h
  have hip := (transverseSpace Ω).inner_orthogonalProjectionOnto_eq_of_mem_left
    ((transverseCurlCurl Ω).adjoint y) (u : testL2Closure Ω)
  have hp := transverseCurlCurl_projection Ω u
  calc
    _ = inner ℂ ((transverseCurlCurl Ω).adjoint y)
        ((transverseSpace Ω).orthogonalProjectionOnto u) := hip.symm
    _ = inner ℂ (y : transverseSpace Ω)
        (transverseCurlCurl Ω (domainTransverseProjection Ω u)) := h
    _ = _ := congrArg (fun z : testL2Closure Ω =>
      inner ℂ ((y : transverseSpace Ω) : testL2Closure Ω) z) hp

/-- Eliminating the full kernel preserves self-adjointness on its literal
orthogonal complement, with no assumed Fourier decomposition. -/
theorem transverseCurlCurl_selfAdjoint (Ω : Opens Space) :
    IsSelfAdjoint (transverseCurlCurl Ω) := by
  have heq := LinearPMap.isSelfAdjoint_def.mp (pecCurlCurl_selfAdjoint Ω)
  have hmem (y : (transverseCurlCurl Ω).adjoint.domain) :
      (y : transverseSpace Ω) ∈ (transverseCurlCurl Ω).domain := by
    have hm : ((y : transverseSpace Ω) : testL2Closure Ω) ∈ (pecCurlCurl Ω).adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _
        ⟨((transverseCurlCurl Ω).adjoint y : testL2Closure Ω), transverse_adjoint_test Ω y⟩
    change ((y : transverseSpace Ω) : testL2Closure Ω) ∈ (pecCurlCurl Ω).domain
    rwa [heq] at hm
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨fun y hy => hmem ⟨y, hy⟩, ?_⟩
    intro y x hxy
    apply Subtype.ext
    have htarget : pecCurlCurl Ω (transverseDomainInclusion Ω x) =
        ((transverseCurlCurl Ω).adjoint y : testL2Closure Ω) := by
      apply (pecCurlCurl_dense Ω).eq_of_inner_left ℂ
      intro v hv
      have hs := (pecFormEmbedding Ω).operator_symmetric
        (transverseDomainInclusion Ω x) ⟨v, hv⟩
      change inner ℂ (pecCurlCurl Ω (transverseDomainInclusion Ω x)) v =
        inner ℂ ((x : transverseSpace Ω) : testL2Closure Ω) (pecCurlCurl Ω ⟨v, hv⟩) at hs
      have ht := transverse_adjoint_test Ω y ⟨v, hv⟩
      have ht' := ht.trans (congrArg (fun z : transverseSpace Ω =>
        inner ℂ (z : testL2Closure Ω) (pecCurlCurl Ω ⟨v, hv⟩)) hxy)
      exact hs.trans ht'.symm
    exact htarget.symm
  · exact (transverseCurlCurl_symmetric Ω).le_adjoint (transverseCurlCurl_dense Ω)

theorem transverseCurlCurl_closed (Ω : Opens Space) :
    (transverseCurlCurl Ω).IsClosed := (transverseCurlCurl_selfAdjoint Ω).isClosed

end Maxwell.Continuum
