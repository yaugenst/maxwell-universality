import Maxwell.Continuum.InvariantRestrictionTransport
import Maxwell.Continuum.HighSchurRange

/-! Closed range transported from the actual finite-low/high decomposition. -/

noncomputable section

namespace Maxwell.Continuum.InvariantRestriction.Data

open FormPerturbation SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} {K : Submodule ℂ H} [CompleteSpace K]
variable [FiniteDimensional ℂ K]
variable (F : InvariantRestriction.Data A K) (hA : IsSelfAdjoint A)
variable (B : H →L[ℂ] H) (hB : B.IsSymmetric)

include hB in
theorem mem_range_iff_block (f : H) :
    f ∈ (addBounded A B).toFun.range ↔
      K.orthogonalDecomposition f ∈ (F.blockOperator hA B).toFun.range := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨F.domainEquiv hA u, (F.block_intertwine hA B hB u).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨(F.domainEquiv hA).symm v, ?_⟩
    exact (F.block_intertwine_symm hA B hB v).trans
      ((congrArg K.orthogonalDecomposition.symm hv).trans
        (K.orthogonalDecomposition.symm_apply_apply f))

include F hA hB in
theorem range_isClosed (R : BoundedInverse (F.highBlock hA B)) :
    IsClosed ((addBounded A B).toFun.range : Set H) := by
  have heq : ((addBounded A B).toFun.range : Set H) =
      K.orthogonalDecomposition ⁻¹' ((F.blockOperator hA B).toFun.range : Set _) := by
    ext f
    exact F.mem_range_iff_block hA B hB f
  rw [heq]
  exact (HighSchur.range_isClosed (F.lowBlock B) (coupling (K := K) B) R).preimage
    K.orthogonalDecomposition.continuous

end Maxwell.Continuum.InvariantRestriction.Data
