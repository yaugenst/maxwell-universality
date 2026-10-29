import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Representation of a closed nonnegative form

The form domain is a Hilbert space `V` embedded densely and injectively into
the ambient Hilbert space `H`. Its Hilbert inner product is the shifted form
inner product. The bounded shifted resolvent is `j ∘ j.adjoint`; inversion on
its range produces the unbounded represented operator.

This construction works over both `ℝ` and `ℂ`. It will be instantiated with
the closed PEC weak-curl graph, rather than with a discrete Maxwell matrix.
-/

noncomputable section

namespace Maxwell.Continuum

open scoped InnerProductSpace

variable {𝕜 V H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A Hilbert form domain embedded in the ambient Hilbert space. The
contractivity hypothesis expresses nonnegativity of the unshifted form. -/
structure FormEmbedding (𝕜 : Type*) (V H : Type*) [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] where
  inclusion : V →L[𝕜] H
  injective : Function.Injective inclusion
  dense : DenseRange inclusion
  contractive : ∀ v, ‖inclusion v‖ ≤ ‖v‖

namespace FormEmbedding

set_option backward.isDefEq.respectTransparency false

variable (F : FormEmbedding 𝕜 V H)

/-- The unshifted closed form. -/
def form (u v : V) : 𝕜 :=
  inner 𝕜 u v - inner 𝕜 (F.inclusion u) (F.inclusion v)

/-- The variational solution operator into the form domain. -/
def variationalSolution : H →L[𝕜] V := F.inclusion.adjoint

/-- The bounded inverse of the represented operator shifted by identity. -/
def resolvent : H →L[𝕜] H := F.inclusion.comp F.variationalSolution

theorem variationalSolution_spec (f : H) (v : V) :
    inner 𝕜 (F.variationalSolution f) v = inner 𝕜 f (F.inclusion v) :=
  F.inclusion.adjoint_inner_left v f

theorem variationalSolution_unique (f : H) (u : V)
    (hu : ∀ v, inner 𝕜 u v = inner 𝕜 f (F.inclusion v)) :
    u = F.variationalSolution f := by
  apply ext_inner_right 𝕜
  intro v
  rw [hu, F.variationalSolution_spec]

theorem variationalSolution_injective : Function.Injective F.variationalSolution := by
  intro f g h
  apply F.dense.eq_of_inner_left 𝕜
  intro v
  rw [← F.variationalSolution_spec, ← F.variationalSolution_spec, h]

theorem resolvent_injective : Function.Injective F.resolvent :=
  F.injective.comp F.variationalSolution_injective

theorem resolvent_symmetric : F.resolvent.IsSymmetric := by
  intro f g
  change inner 𝕜 (F.inclusion (F.inclusion.adjoint f)) g =
    inner 𝕜 f (F.inclusion (F.inclusion.adjoint g))
  rw [← F.inclusion.adjoint_inner_right, F.inclusion.adjoint_inner_left]

theorem resolvent_dense : DenseRange F.resolvent := by
  change Dense (F.resolvent.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have h := F.resolvent.orthogonal_ker
  rw [F.resolvent_symmetric.clm_adjoint_eq] at h
  rw [← h,
    LinearMap.ker_eq_bot.mpr F.resolvent_injective, Submodule.bot_orthogonal_eq_top]

/-- The inverse of the shifted resolvent on its range. -/
def inverseOnRange : F.resolvent.range →ₗ[𝕜] H :=
  (LinearEquiv.ofInjective F.resolvent.toLinearMap F.resolvent_injective).symm.toLinearMap

@[simp]
theorem resolvent_inverseOnRange (x : F.resolvent.range) :
    F.resolvent (F.inverseOnRange x) = x :=
  LinearEquiv.ofInjective_symm_apply _ x

@[simp]
theorem inverseOnRange_resolvent (f : H) :
    F.inverseOnRange ⟨F.resolvent f, LinearMap.mem_range_self _ f⟩ = f := by
  apply F.resolvent_injective
  simp

/-- The closed-form represented operator, with its full unbounded domain. -/
def operator : H →ₗ.[𝕜] H where
  domain := F.resolvent.range
  toFun := F.inverseOnRange - F.resolvent.range.subtype

@[simp]
theorem operator_apply (x : F.operator.domain) :
    F.operator x = F.inverseOnRange x - (x : H) := rfl

@[simp]
theorem operator_resolvent (f : H) :
    F.operator ⟨F.resolvent f, LinearMap.mem_range_self _ f⟩ = f - F.resolvent f := by
  change F.inverseOnRange ⟨F.resolvent f, LinearMap.mem_range_self _ f⟩ -
    F.resolvent f = f - F.resolvent f
  rw [F.inverseOnRange_resolvent]

theorem operator_dense : Dense (F.operator.domain : Set H) := F.resolvent_dense

theorem resolvent_operator (x : F.operator.domain) :
    F.resolvent (F.operator x + (x : H)) = x := by
  rw [F.operator_apply, sub_add_cancel, F.resolvent_inverseOnRange]

theorem inclusion_norm_le_one : ‖F.inclusion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa only [one_mul] using F.contractive

theorem variationalSolution_norm_le (f : H) : ‖F.variationalSolution f‖ ≤ ‖f‖ := by
  calc
    ‖F.variationalSolution f‖ ≤ ‖F.variationalSolution‖ * ‖f‖ :=
      F.variationalSolution.le_opNorm f
    _ ≤ 1 * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      simpa only [variationalSolution, LinearIsometryEquiv.norm_map] using
        F.inclusion_norm_le_one
    _ = ‖f‖ := one_mul _

theorem resolvent_norm_le (f : H) : ‖F.resolvent f‖ ≤ ‖f‖ :=
  (F.contractive (F.variationalSolution f)).trans (F.variationalSolution_norm_le f)

theorem resolvent_norm_le_one : ‖F.resolvent‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa only [one_mul] using F.resolvent_norm_le

theorem operator_symmetric : F.operator.IsFormalAdjoint F.operator := by
  intro x y
  rw [F.operator_apply, F.operator_apply, inner_sub_left, inner_sub_right]
  congr 1
  calc
    inner 𝕜 (F.inverseOnRange x) (y : H) =
        inner 𝕜 (F.inverseOnRange x) (F.resolvent (F.inverseOnRange y)) := by
      rw [F.resolvent_inverseOnRange]
    _ = inner 𝕜 (F.resolvent (F.inverseOnRange x)) (F.inverseOnRange y) :=
      (F.resolvent_symmetric _ _).symm
    _ = inner 𝕜 (x : H) (F.inverseOnRange y) := by
      rw [F.resolvent_inverseOnRange]

theorem adjoint_resolvent_identity (y : F.operator.adjoint.domain) :
    F.resolvent (F.operator.adjoint y + (y : H)) = y := by
  apply ext_inner_right 𝕜
  intro f
  have h := (LinearPMap.adjoint_isFormalAdjoint F.operator_dense) y
    ⟨F.resolvent f, LinearMap.mem_range_self _ f⟩
  change inner 𝕜 (F.operator.adjoint y) (F.resolvent f) =
    inner 𝕜 (y : H) (F.operator ⟨F.resolvent f, LinearMap.mem_range_self _ f⟩) at h
  rw [F.operator_resolvent, inner_sub_right] at h
  calc
    inner 𝕜 (F.resolvent (F.operator.adjoint y + (y : H))) f =
        inner 𝕜 (F.operator.adjoint y + (y : H)) (F.resolvent f) :=
      F.resolvent_symmetric _ _
    _ = inner 𝕜 (y : H) f := by
      rw [inner_add_left, h, sub_add_cancel]

/-- The represented operator is genuinely self-adjoint, with equality of
operator domains, not just symmetric on a test core. -/
theorem operator_selfAdjoint : IsSelfAdjoint F.operator := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      exact ⟨F.operator.adjoint ⟨y, hy⟩ + y, F.adjoint_resolvent_identity ⟨y, hy⟩⟩
    · intro y x hxy
      have hi : F.inverseOnRange x = F.operator.adjoint y + (y : H) := by
        apply F.resolvent_injective
        rw [F.resolvent_inverseOnRange, F.adjoint_resolvent_identity]
        exact hxy.symm
      rw [F.operator_apply, hi, hxy, add_sub_cancel_right]
  · exact F.operator_symmetric.le_adjoint F.operator_dense

theorem operator_closed : F.operator.IsClosed := F.operator_selfAdjoint.isClosed

/-- Every vector in the operator domain satisfies precisely the original
variational equation on the entire form domain. -/
theorem operator_weak (x : F.operator.domain) :
    ∃ u : V, F.inclusion u = (x : H) ∧
      ∀ v : V, F.form u v = inner 𝕜 (F.operator x) (F.inclusion v) := by
  refine ⟨F.variationalSolution (F.inverseOnRange x), ?_, ?_⟩
  · exact F.resolvent_inverseOnRange x
  · intro v
    rw [form, F.variationalSolution_spec, F.operator_apply, inner_sub_left]
    change inner 𝕜 (F.inverseOnRange x) (F.inclusion v) -
      inner 𝕜 (F.resolvent (F.inverseOnRange x)) (F.inclusion v) = _
    rw [F.resolvent_inverseOnRange]

/-- A weak solution with an ambient-space right-hand side is in the
operator domain. This is the nontrivial direction of form representation. -/
theorem mem_operator_domain_of_weak (u : V) (g : H)
    (hu : ∀ v : V, F.form u v = inner 𝕜 g (F.inclusion v)) :
    F.inclusion u ∈ F.operator.domain := by
  have hv : u = F.variationalSolution (g + F.inclusion u) := by
    apply F.variationalSolution_unique
    intro v
    rw [inner_add_left]
    exact sub_eq_iff_eq_add.mp (hu v)
  refine ⟨g + F.inclusion u, ?_⟩
  change F.inclusion (F.variationalSolution (g + F.inclusion u)) = F.inclusion u
  rw [← hv]

/-- The represented operator takes exactly the given weak right-hand side. -/
theorem operator_eq_of_weak (u : V) (g : H)
    (hu : ∀ v : V, F.form u v = inner 𝕜 g (F.inclusion v))
    (hx : F.inclusion u ∈ F.operator.domain) :
    F.operator ⟨F.inclusion u, hx⟩ = g := by
  obtain ⟨w, hw, hweak⟩ := F.operator_weak ⟨F.inclusion u, hx⟩
  have hwu : w = u := F.injective hw
  apply F.dense.eq_of_inner_left 𝕜
  intro v
  rw [← hweak, hwu, hu]

/-- Exact operator-graph characterization by the original weak form. -/
theorem operator_graph_iff (x g : H) :
    (∃ hx : x ∈ F.operator.domain, F.operator ⟨x, hx⟩ = g) ↔
      ∃ u : V, F.inclusion u = x ∧
        ∀ v : V, F.form u v = inner 𝕜 g (F.inclusion v) := by
  constructor
  · rintro ⟨hx, rfl⟩
    exact F.operator_weak ⟨x, hx⟩
  · rintro ⟨u, rfl, hu⟩
    exact ⟨F.mem_operator_domain_of_weak u g hu,
      F.operator_eq_of_weak u g hu _⟩

theorem form_nonnegative (u : V) : 0 ≤ RCLike.re (F.form u u) := by
  rw [form, map_sub, inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  exact sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (F.contractive u) 2)

theorem operator_nonnegative (x : F.operator.domain) :
    0 ≤ RCLike.re (inner 𝕜 (F.operator x) (x : H)) := by
  obtain ⟨u, hu, hweak⟩ := F.operator_weak x
  rw [← hu, ← hweak]
  exact F.form_nonnegative u

end FormEmbedding

end Maxwell.Continuum
