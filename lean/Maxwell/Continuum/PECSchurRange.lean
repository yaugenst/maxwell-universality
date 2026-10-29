import Maxwell.Continuum.PECFiniteSpectrum
import Maxwell.Continuum.InvariantRestrictionRange

/-! Closed range for the full physical Maxwell operator, including at
eigenvalues. Both elimination steps use the actual operator domains. -/

noncomputable section

namespace Maxwell.Continuum.ScalarDielectric

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace SelfAdjointResolvent

variable (ε : ScalarDielectric) (Ω : Opens Space)
variable (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)

theorem maxwell_mem_range_iff_schur (f : testL2Closure Ω) :
    f ∈ (shift (maxwellOperator Ω ε) ell).toFun.range ↔
      ε.schurSource Ω ell hell f ∈ (ε.schurOperator Ω ell hell).toFun.range := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨domainTransverseProjection Ω u,
      ((ε.maxwell_equation_iff_schur Ω ell hell u _).mp rfl).2⟩
  · rintro ⟨t, ht⟩
    let g := -ε.gradientResolvent Ω ell hell
      (gradientProjection Ω f + ε.materialCoupling Ω t)
    refine ⟨kernelAssembleDomain Ω g t,
      (ε.maxwell_equation_iff_schur Ω ell hell _ f).mpr ?_⟩
    constructor
    · exact (gradientProjection_assemble Ω g t).trans
        (congrArg (fun z : transverseSpace Ω =>
          -ε.gradientResolvent Ω ell hell (gradientProjection Ω f + ε.materialCoupling Ω z))
          (transverseProjection_assemble Ω g t).symm)
    · exact (congrArg (ε.schurOperator Ω ell hell).toFun
        (domainTransverseProjection_assemble Ω g t)).trans ht

theorem maxwell_range_closed_of_schur
    (hclosed : IsClosed ((ε.schurOperator Ω ell hell).toFun.range : Set (transverseSpace Ω))) :
    IsClosed ((shift (maxwellOperator Ω ε) ell).toFun.range : Set (testL2Closure Ω)) := by
  have heq : ((shift (maxwellOperator Ω ε) ell).toFun.range : Set (testL2Closure Ω)) =
      (ε.schurSource Ω ell hell) ⁻¹'
        ((ε.schurOperator Ω ell hell).toFun.range : Set (transverseSpace Ω)) := by
    ext f
    exact ε.maxwell_mem_range_iff_schur Ω ell hell f
  rw [heq]
  exact hclosed.preimage (ε.schurSource Ω ell hell).continuous

/-- The actual Maxwell range is closed at every point of the counting
window, even where the operator has a nontrivial finite kernel. -/
theorem window_range_isClosed (D : TransverseCutoff Ω) (t : SpectralWindow) :
    IsClosed ((shift (maxwellOperator Ω ε) t).toFun.range : Set (testL2Closure Ω)) := by
  apply ε.maxwell_range_closed_of_schur Ω t t.property.1
  exact D.invariant.range_isClosed (transverseCurlCurl_selfAdjoint Ω)
    (ε.transverseSchurPart Ω t t.property.1)
    (ε.transverseSchurPart_symmetric Ω t t.property.1)
    ((ε.cutoffFamily Ω D).highInverse D.invariant (transverseCurlCurl_selfAdjoint Ω) t)

end Maxwell.Continuum.ScalarDielectric
