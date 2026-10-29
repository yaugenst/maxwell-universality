import Maxwell.Continuum.FormRepresentation

/-!
# Bounded symmetric perturbations preserve self-adjointness

The unbounded operator keeps exactly its original domain. This is the
operator-theoretic step used to pass from PEC curl-curl to curl-curl minus a
bounded real scalar dielectric multiplier.
-/

noncomputable section

namespace Maxwell.Continuum

open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

namespace FormPerturbation

set_option backward.isDefEq.respectTransparency false

/-- Add a bounded operator without changing the unbounded operator domain. -/
def addBounded (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H) : H →ₗ.[𝕜] H where
  domain := A.domain
  toFun := A.toFun + B.toLinearMap.comp A.domain.subtype

@[simp]
theorem addBounded_domain (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H) :
    (addBounded A B).domain = A.domain := rfl

@[simp]
theorem addBounded_apply (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (x : (addBounded A B).domain) :
    addBounded A B x = A x + B (x : H) := rfl

theorem addBounded_symmetric (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (hA : A.IsFormalAdjoint A) (hB : B.IsSymmetric) :
    (addBounded A B).IsFormalAdjoint (addBounded A B) := by
  intro x y
  rw [addBounded_apply, addBounded_apply, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·) (hA x y) (hB (x : H) (y : H))

variable [CompleteSpace H]

theorem adjoint_test (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (hA : Dense (A.domain : Set H)) (hB : B.IsSymmetric)
    (y : (addBounded A B).adjoint.domain) (x : A.domain) :
    inner 𝕜 ((addBounded A B).adjoint y - B (y : H)) (x : H) =
      inner 𝕜 (y : H) (A x) := by
  have h := (LinearPMap.adjoint_isFormalAdjoint
    (show Dense ((addBounded A B).domain : Set H) from hA)) y x
  rw [addBounded_apply, inner_add_right] at h
  calc
    inner 𝕜 ((addBounded A B).adjoint y - B (y : H)) (x : H) =
        inner 𝕜 ((addBounded A B).adjoint y) (x : H) -
          inner 𝕜 (B (y : H)) (x : H) := inner_sub_left _ _ _
    _ = (inner 𝕜 (y : H) (A x) + inner 𝕜 (y : H) (B (x : H))) -
          inner 𝕜 (y : H) (B (x : H)) := by
      rw [h]
      exact congrArg (fun z => inner 𝕜 (y : H) (A x) +
        inner 𝕜 (y : H) (B (x : H)) - z) (hB (y : H) (x : H))
    _ = inner 𝕜 (y : H) (A x) := add_sub_cancel_right _ _

/-- Bounded symmetric perturbation theorem with equality of the actual
adjoint domain, valid over real or complex Hilbert spaces. -/
theorem addBounded_selfAdjoint (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (hA : IsSelfAdjoint A) (hB : B.IsSymmetric) :
    IsSelfAdjoint (addBounded A B) := by
  have hAeq := LinearPMap.isSelfAdjoint_def.mp hA
  have hAsym : A.IsFormalAdjoint A := by
    simpa only [hAeq] using LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  have hmem (y : (addBounded A B).adjoint.domain) : (y : H) ∈ A.domain := by
    have hm : (y : H) ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _
        ⟨(addBounded A B).adjoint y - B (y : H), adjoint_test A B hA.dense_domain hB y⟩
    rwa [hAeq] at hm
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨fun y hy => hmem ⟨y, hy⟩, ?_⟩
    intro y x hxy
    have ht : A x = (addBounded A B).adjoint y - B (y : H) := by
      apply hA.dense_domain.eq_of_inner_left 𝕜
      intro v hv
      calc
        inner 𝕜 (A x) v = inner 𝕜 (x : H) (A ⟨v, hv⟩) := hAsym x ⟨v, hv⟩
        _ = inner 𝕜 (y : H) (A ⟨v, hv⟩) := by rw [hxy]
        _ = inner 𝕜 ((addBounded A B).adjoint y - B (y : H)) v :=
          (adjoint_test A B hA.dense_domain hB y ⟨v, hv⟩).symm
    rw [addBounded_apply, ht, hxy, sub_add_cancel]
  · exact (addBounded_symmetric A B hAsym hB).le_adjoint hA.dense_domain

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- Exact weak-form characterization after adding a bounded perturbation.
In particular, an ambient-space weak solution is automatically in the full
unbounded operator domain. -/
theorem addBounded_graph_iff (F : FormEmbedding 𝕜 V H) (B : H →L[𝕜] H)
    (x f : H) :
    (∃ hx : x ∈ (addBounded F.operator B).domain,
      addBounded F.operator B ⟨x, hx⟩ = f) ↔
      ∃ u : V, F.inclusion u = x ∧
        ∀ v : V, F.form u v + inner 𝕜 (B x) (F.inclusion v) =
          inner 𝕜 f (F.inclusion v) := by
  constructor
  · rintro ⟨hx, hf⟩
    obtain ⟨u, hu, hweak⟩ := F.operator_weak ⟨x, hx⟩
    refine ⟨u, hu, fun v => ?_⟩
    rw [hweak, ← inner_add_left]
    exact congrArg (fun z => inner 𝕜 z (F.inclusion v)) hf
  · rintro ⟨u, rfl, hu⟩
    have hw : ∀ v : V, F.form u v = inner 𝕜 (f - B (F.inclusion u))
        (F.inclusion v) := by
      intro v
      rw [inner_sub_left]
      exact eq_sub_iff_add_eq.mpr (hu v)
    have hx := F.mem_operator_domain_of_weak u (f - B (F.inclusion u)) hw
    refine ⟨hx, ?_⟩
    rw [addBounded_apply, F.operator_eq_of_weak u _ hw, sub_add_cancel]

end FormPerturbation

end Maxwell.Continuum
