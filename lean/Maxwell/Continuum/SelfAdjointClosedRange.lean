import Maxwell.Continuum.InvariantRestriction
import Maxwell.Continuum.SelfAdjointRightInverse

/-! A closed-range self-adjoint operator has a bounded inverse on the
orthogonal complement of its actual kernel. -/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def graphEquivOfBijective (A : H →ₗ.[ℂ] H) (hclosed : A.IsClosed)
    (hbij : Function.Bijective A) : GraphNorm.space A ≃L[ℂ] H := by
  letI : CompleteSpace (GraphNorm.space A) :=
    (GraphNorm.space_isClosed hclosed).completeSpace_coe
  apply ContinuousLinearEquiv.ofBijective (GraphNorm.action A)
  · apply LinearMap.ker_eq_bot.mpr
    intro u v huv
    apply GraphNorm.inclusion_injective A
    have h := hbij.1 ((GraphNorm.action_eq A u).trans
      (huv.trans (GraphNorm.action_eq A v).symm))
    exact congrArg Subtype.val h
  · rw [graph_action_range]
    exact LinearMap.range_eq_top.mpr hbij.2

def BoundedInverse.ofBijective (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hbij : Function.Bijective A) : BoundedInverse A :=
  BoundedInverse.ofRightInverse A hA
    ((GraphNorm.inclusion A).comp
      (graphEquivOfBijective A hA.isClosed hbij).symm.toContinuousLinearMap)
    (fun _ => GraphNorm.inclusion_mem_domain A _)
    (fun f => (GraphNorm.action_eq A _).trans
      ((graphEquivOfBijective A hA.isClosed hbij).apply_symm_apply f))

omit [CompleteSpace H] in
theorem kernelRestriction (A : H →ₗ.[ℂ] H) : InvariantRestriction.Data A A.ker := by
  refine ⟨A.ker_le_domain, ?_⟩
  intro x
  have h : A ⟨(x : H), A.ker_le_domain x.property⟩ = 0 :=
    LinearPMap.coe_mem_ker_iff.mp x.property
  rw [h]
  exact A.ker.zero_mem

theorem range_eq_kernel_orthogonal (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hclosed : IsClosed (A.toFun.range : Set H)) : A.toFun.range = A.kerᗮ := by
  have h := orthogonal_range_eq_adjoint_ker A hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at h
  rw [← h, Submodule.orthogonal_orthogonal_eq_closure]
  exact hclosed.submodule_topologicalClosure_eq.symm

variable (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) [CompleteSpace A.ker]

theorem kernelHigh_surjective (hclosed : IsClosed (A.toFun.range : Set H)) :
    Function.Surjective ((kernelRestriction A).highOperator hA) := by
  intro y
  have hy : (y : H) ∈ A.toFun.range := by
    rw [range_eq_kernel_orthogonal A hA hclosed]
    exact y.property
  obtain ⟨u, hu⟩ := hy
  refine ⟨(kernelRestriction A).domainHighProjection u, ?_⟩
  exact ((kernelRestriction A).highProjection_action hA u).trans
    ((congrArg A.kerᗮ.orthogonalProjectionOnto hu).trans
      (A.kerᗮ.orthogonalProjectionOnto_mem_subspace_eq_self y))

/-- Closed range constructs an actual two-sided inverse on the kernel
complement. The inverse laws refer to the induced unbounded domain. -/
def kernelHighInverse (hclosed : IsClosed (A.toFun.range : Set H)) :
    BoundedInverse ((kernelRestriction A).highOperator hA) :=
  BoundedInverse.ofBijective _ ((kernelRestriction A).high_selfAdjoint hA)
    ⟨injective_of_surjective _ ((kernelRestriction A).high_selfAdjoint hA)
      (kernelHigh_surjective A hA hclosed), kernelHigh_surjective A hA hclosed⟩

include hA in
/-- A quantitative lower norm bound follows on the kernel complement.
The finite constant is derived from a constructed bounded inverse. -/
theorem kernel_complement_bound (hclosed : IsClosed (A.toFun.range : Set H)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : A.domain, (u : H) ∈ A.kerᗮ → ‖(u : H)‖ ≤ C * ‖A u‖ := by
  let R := kernelHighInverse A hA hclosed
  refine ⟨‖R.map‖ + 1, by positivity, ?_⟩
  intro u hu
  let t : ((kernelRestriction A).highOperator hA).domain := ⟨⟨u, hu⟩, u.property⟩
  have hi := R.map_apply t
  calc
    ‖(u : H)‖ = ‖R.map (((kernelRestriction A).highOperator hA) t)‖ :=
      (congrArg norm hi).symm
    _ ≤ ‖R.map‖ * ‖((kernelRestriction A).highOperator hA) t‖ := R.map.le_opNorm _
    _ ≤ (‖R.map‖ + 1) * ‖A u‖ := by
      change ‖R.map‖ * ‖A u‖ ≤ (‖R.map‖ + 1) * ‖A u‖
      nlinarith [norm_nonneg (A u)]

end Maxwell.Continuum.SelfAdjointResolvent
