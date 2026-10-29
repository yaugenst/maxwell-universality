import Maxwell.Continuum.PECOperator

/-! The zero-curl subspace of the actual PEC operator is closed. -/

noncomputable section

namespace Maxwell.Continuum

open TopologicalSpace

theorem closed_operator_kernel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : H →ₗ.[ℂ] H) (hC : C.IsClosed) : IsClosed (C.ker : Set H) := by
  have heq : (C.ker : Set H) = (fun x : H => (x, (0 : H))) ⁻¹' (C.graph : Set (H × H)) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, C.mem_ker_iff, C.mem_graph_iff]
    constructor
    · rintro ⟨y, hxy, hy⟩
      exact ⟨y, hxy.symm, hy⟩
    · rintro ⟨y, hyx, hy⟩
      exact ⟨y, hyx.symm, hy⟩
  rw [heq]
  exact hC.preimage (continuous_id.prodMk continuous_const)

/-- The kernel is retained as an infinite closed subspace. -/
abbrev gradientSpace (Ω : Opens Space) : Submodule ℂ (testL2Closure Ω) :=
  (pecCurlCurl Ω).ker

theorem gradientSpace_isClosed (Ω : Opens Space) :
    IsClosed (gradientSpace Ω : Set (testL2Closure Ω)) :=
  closed_operator_kernel _ (pecCurlCurl_closed Ω)

instance (Ω : Opens Space) : CompleteSpace (gradientSpace Ω) :=
  (gradientSpace_isClosed Ω).completeSpace_coe

abbrev transverseSpace (Ω : Opens Space) : Submodule ℂ (testL2Closure Ω) :=
  (gradientSpace Ω)ᗮ

instance (Ω : Opens Space) : CompleteSpace (transverseSpace Ω) :=
  (gradientSpace Ω).isClosed_orthogonal.completeSpace_coe

/-- Zero operator modes are exactly the PEC fields with zero weak curl. -/
theorem mem_gradientSpace_iff (Ω : Opens Space) (u : testL2Closure Ω) :
    u ∈ gradientSpace Ω ↔
      ∃ v : pecGraph Ω, pecDomainInclusion Ω v = u ∧ pecCurl Ω v = 0 := by
  constructor
  · intro hu
    obtain ⟨y, huy, hy⟩ := (pecCurlCurl Ω).mem_ker_iff.mp hu
    have hg : ∃ h : u ∈ (pecCurlCurl Ω).domain, pecCurlCurl Ω ⟨u, h⟩ = 0 := by
      subst u
      exact ⟨y.property, hy⟩
    obtain ⟨v, hv, hform⟩ := (pecCurlCurl_graph_iff Ω u 0).mp hg
    refine ⟨v, hv, ?_⟩
    have hn := hform v
    rw [inner_zero_left] at hn
    exact inner_self_eq_zero.mp hn
  · rintro ⟨v, hv, hcurl⟩
    have hg : ∃ h : u ∈ (pecCurlCurl Ω).domain, pecCurlCurl Ω ⟨u, h⟩ = 0 := by
      apply (pecCurlCurl_graph_iff Ω u 0).mpr
      refine ⟨v, hv, ?_⟩
      intro w
      simp only [hcurl, inner_zero_left]
    obtain ⟨hu, heq⟩ := hg
    exact (pecCurlCurl Ω).mem_ker_iff.mpr ⟨⟨u, hu⟩, rfl, heq⟩

theorem gradient_mem_domain (Ω : Opens Space) (g : gradientSpace Ω) :
    (g : testL2Closure Ω) ∈ (pecCurlCurl Ω).domain :=
  (pecCurlCurl Ω).ker_le_domain g.property

theorem pecCurlCurl_gradient (Ω : Opens Space) (g : gradientSpace Ω) :
    pecCurlCurl Ω ⟨g, gradient_mem_domain Ω g⟩ = 0 :=
  (pecCurlCurl Ω).coe_mem_ker_iff.mp g.property

end Maxwell.Continuum
