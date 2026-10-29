import Maxwell.Continuum.GraphNorm
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Inverses of unbounded self-adjoint operators from a lower norm bound

For the actual partially defined operator, a positive estimate
`δ * ‖x‖ ≤ ‖A x‖` implies closed range. The orthogonal complement of the
range is the kernel of the adjoint, so self-adjointness makes that range all
of the Hilbert space. This constructs an inverse instead of assuming one.

The link from distance to the spectrum to the lower norm bound is separate;
no spectral theorem or spectral-distance estimate is assumed here.
-/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The usual range-adjoint-kernel identity for a genuinely unbounded,
densely defined operator. -/
theorem orthogonal_range_eq_adjoint_ker (A : H →ₗ.[𝕜] H)
    (hA : Dense (A.domain : Set H)) : A.toFun.rangeᗮ = A.adjoint.ker := by
  ext y
  constructor
  · intro hy
    have ht (x : A.domain) : inner 𝕜 (0 : H) (x : H) = inner 𝕜 y (A x) := by
      rw [inner_zero_left]
      exact (inner_eq_zero_symm.mp (hy (A x) ⟨x, rfl⟩)).symm
    have hm : y ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists y ⟨0, ht⟩
    exact LinearPMap.mem_ker_iff.mpr
      ⟨⟨y, hm⟩, rfl, LinearPMap.adjoint_apply_eq hA ⟨y, hm⟩ ht⟩
  · intro hker
    obtain ⟨z, hzy, hz⟩ := LinearPMap.mem_ker_iff.mp hker
    subst y
    rintro _ ⟨x, rfl⟩
    change inner 𝕜 (A x) (z : H) = 0
    rw [inner_eq_zero_symm]
    exact ((LinearPMap.adjoint_isFormalAdjoint hA) z x).symm.trans
      (by rw [hz, inner_zero_left])

omit [CompleteSpace H] in
theorem graph_action_range (A : H →ₗ.[𝕜] H) :
    (GraphNorm.action A).range = A.toFun.range := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨⟨GraphNorm.inclusion A u, GraphNorm.inclusion_mem_domain A u⟩,
      GraphNorm.action_eq A u⟩
  · rintro ⟨u, rfl⟩
    exact ⟨⟨WithLp.toLp 2 ((u : H), A u), A.mem_graph u⟩, rfl⟩

variable (A : H →ₗ.[𝕜] H) {δ : ℝ} (hδ : 0 < δ)
variable (hbound : ∀ x : A.domain, δ * ‖(x : H)‖ ≤ ‖A x‖)

include hδ hbound

omit [CompleteSpace H] in
/-- The graph norm is controlled by the operator output. -/
theorem graph_norm_le (u : GraphNorm.space A) :
    ‖u‖ ≤ (δ⁻¹ + 1) * ‖GraphNorm.action A u‖ := by
  have h := hbound ⟨GraphNorm.inclusion A u, GraphNorm.inclusion_mem_domain A u⟩
  rw [GraphNorm.action_eq] at h
  have hi : ‖GraphNorm.inclusion A u‖ ≤ δ⁻¹ * ‖GraphNorm.action A u‖ := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hδ), one_mul] using h
  calc
    ‖u‖ ≤ ‖GraphNorm.inclusion A u‖ + ‖GraphNorm.action A u‖ := GraphNorm.norm_le_sum A u
    _ ≤ δ⁻¹ * ‖GraphNorm.action A u‖ + ‖GraphNorm.action A u‖ := add_le_add hi le_rfl
    _ = (δ⁻¹ + 1) * ‖GraphNorm.action A u‖ := by ring

omit [CompleteSpace H] in
theorem graph_action_antilipschitz :
    AntilipschitzWith ⟨δ⁻¹ + 1, by positivity⟩ (GraphNorm.action A) :=
  (GraphNorm.action A).antilipschitz_of_bound (graph_norm_le A hδ hbound)

/-- A closed operator with a positive lower norm bound has closed range. -/
theorem range_isClosed (hclosed : A.IsClosed) : IsClosed (A.toFun.range : Set H) := by
  let : CompleteSpace (GraphNorm.space A) :=
    (GraphNorm.space_isClosed hclosed).completeSpace_coe
  rw [← graph_action_range]
  exact (graph_action_antilipschitz A hδ hbound).isClosed_range
    (GraphNorm.action A).uniformContinuous

omit [CompleteSpace H] in
theorem ker_eq_bot : A.ker = ⊥ := by
  rw [LinearPMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  apply norm_eq_zero.mp
  have h := hbound x
  rw [hx, norm_zero] at h
  nlinarith [norm_nonneg (x : H)]

/-- Self-adjointness turns the positive lower norm bound into surjectivity. -/
theorem range_eq_top (hA : IsSelfAdjoint A) : A.toFun.range = ⊤ := by
  have hclosed := range_isClosed A hδ hbound hA.isClosed
  have horth : A.toFun.rangeᗮ = ⊥ := by
    rw [orthogonal_range_eq_adjoint_ker A hA.dense_domain,
      LinearPMap.isSelfAdjoint_def.mp hA, ker_eq_bot A hδ hbound]
  have hclosure : A.toFun.range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth,
      Submodule.bot_orthogonal_eq_top]
  rwa [hclosed.submodule_topologicalClosure_eq] at hclosure

theorem surjective (hA : IsSelfAdjoint A) : Function.Surjective A :=
  LinearMap.range_eq_top.mp (range_eq_top A hδ hbound hA)

/-- A Hilbert graph-space equivalence whose inverse is the constructed
unbounded-operator resolvent. -/
def graphEquiv (hA : IsSelfAdjoint A) : GraphNorm.space A ≃L[𝕜] H := by
  letI : CompleteSpace (GraphNorm.space A) :=
    (GraphNorm.space_isClosed hA.isClosed).completeSpace_coe
  exact ContinuousLinearEquiv.ofBijective (GraphNorm.action A)
    (LinearMap.ker_eq_bot.mpr (graph_action_antilipschitz A hδ hbound).injective)
    (by rw [graph_action_range]; exact range_eq_top A hδ hbound hA)

/-- The inverse into the actual complete operator graph. -/
def graphInverse (hA : IsSelfAdjoint A) : H →L[𝕜] GraphNorm.space A :=
  (graphEquiv A hδ hbound hA).symm.toContinuousLinearMap

@[simp]
theorem action_graphInverse (hA : IsSelfAdjoint A) (f : H) :
    GraphNorm.action A (graphInverse A hδ hbound hA f) = f :=
  (graphEquiv A hδ hbound hA).apply_symm_apply f

@[simp]
theorem graphInverse_action (hA : IsSelfAdjoint A) (x : GraphNorm.space A) :
    graphInverse A hδ hbound hA (GraphNorm.action A x) = x :=
  (graphEquiv A hδ hbound hA).symm_apply_apply x

/-- The constructed inverse as an everywhere-defined bounded map on L². -/
def inverse (hA : IsSelfAdjoint A) : H →L[𝕜] H :=
  (GraphNorm.inclusion A).comp (graphInverse A hδ hbound hA)

theorem inverse_mem_domain (hA : IsSelfAdjoint A) (f : H) :
    inverse A hδ hbound hA f ∈ A.domain :=
  GraphNorm.inclusion_mem_domain A _

theorem apply_inverse (hA : IsSelfAdjoint A) (f : H) :
    A ⟨inverse A hδ hbound hA f, inverse_mem_domain A hδ hbound hA f⟩ = f := by
  exact (GraphNorm.action_eq A (graphInverse A hδ hbound hA f)).trans
    (action_graphInverse A hδ hbound hA f)

theorem inverse_norm_le (hA : IsSelfAdjoint A) (f : H) :
    ‖inverse A hδ hbound hA f‖ ≤ δ⁻¹ * ‖f‖ := by
  apply (mul_le_mul_iff_right₀ hδ).mp
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hδ), one_mul]
  have h := hbound ⟨inverse A hδ hbound hA f, inverse_mem_domain A hδ hbound hA f⟩
  rwa [apply_inverse] at h

theorem inverse_opNorm_le (hA : IsSelfAdjoint A) :
    ‖inverse A hδ hbound hA‖ ≤ δ⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hδ.le)
    (inverse_norm_le A hδ hbound hA)

theorem graphInverse_norm_le (hA : IsSelfAdjoint A) (f : H) :
    ‖graphInverse A hδ hbound hA f‖ ≤ (δ⁻¹ + 1) * ‖f‖ := by
  have h := graph_norm_le A hδ hbound (graphInverse A hδ hbound hA f)
  rwa [action_graphInverse] at h

theorem graphInverse_opNorm_le (hA : IsSelfAdjoint A) :
    ‖graphInverse A hδ hbound hA‖ ≤ δ⁻¹ + 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (graphInverse_norm_le A hδ hbound hA)

theorem inverse_apply (hA : IsSelfAdjoint A) (x : A.domain) :
    inverse A hδ hbound hA (A x) = (x : H) := by
  have hinj := LinearPMap.ker_eq_bot.mp (ker_eq_bot A hδ hbound)
  exact congrArg Subtype.val (hinj (apply_inverse A hδ hbound hA (A x)))

/-- Every domain vector has error bounded by its actual residual. -/
theorem residual_bound (hA : IsSelfAdjoint A) (x : A.domain) (f : H) :
    ‖(x : H) - inverse A hδ hbound hA f‖ ≤ δ⁻¹ * ‖A x - f‖ := by
  let y : A.domain := ⟨inverse A hδ hbound hA f, inverse_mem_domain A hδ hbound hA f⟩
  have h := hbound (x - y)
  rw [A.map_sub, apply_inverse] at h
  change δ * ‖(x : H) - inverse A hδ hbound hA f‖ ≤ ‖A x - f‖ at h
  apply (mul_le_mul_iff_right₀ hδ).mp
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hδ), one_mul] using h

end Maxwell.Continuum.SelfAdjointResolvent
