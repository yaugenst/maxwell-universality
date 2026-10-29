import Maxwell.Continuum.SelfAdjointResolventSpectrum

/-!
# Turning an L² resolvent into an inverse on the actual operator graph

The lift uses the equation `C u = f + B u`; no boundedness of `C` on L²
is asserted. The resulting inverse has values in the Hilbert graph of C.
-/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Lift a literal perturbed equation into the unperturbed operator graph. -/
def graphLift (C : H →ₗ.[𝕜] H) (B R : H →L[𝕜] H)
    (hmem : ∀ f, R f ∈ C.domain)
    (heq : ∀ f, C ⟨R f, hmem f⟩ = f + B (R f)) : H →L[𝕜] GraphNorm.space C :=
  (((WithLp.prodContinuousLinearEquiv 2 𝕜 H H).symm.toContinuousLinearMap).comp
    (R.prod (ContinuousLinearMap.id 𝕜 H + B.comp R))).codRestrict (GraphNorm.space C)
    (by
      intro f
      apply C.mem_graph_iff.mpr
      exact ⟨⟨R f, hmem f⟩, rfl, heq f⟩)

@[simp] theorem inclusion_graphLift (C : H →ₗ.[𝕜] H) (B R : H →L[𝕜] H)
    (hmem : ∀ f, R f ∈ C.domain)
    (heq : ∀ f, C ⟨R f, hmem f⟩ = f + B (R f)) (f : H) :
    GraphNorm.inclusion C (graphLift C B R hmem heq f) = R f := rfl

@[simp] theorem action_graphLift (C : H →ₗ.[𝕜] H) (B R : H →L[𝕜] H)
    (hmem : ∀ f, R f ∈ C.domain)
    (heq : ∀ f, C ⟨R f, hmem f⟩ = f + B (R f)) (f : H) :
    GraphNorm.action C (graphLift C B R hmem heq f) = f + B (R f) := rfl

@[simp] theorem perturbed_graphLift (C : H →ₗ.[𝕜] H) (B R : H →L[𝕜] H)
    (hmem : ∀ f, R f ∈ C.domain)
    (heq : ∀ f, C ⟨R f, hmem f⟩ = f + B (R f)) (f : H) :
    GraphNorm.perturbed C B (graphLift C B R hmem heq f) = f := by
  simp only [GraphNorm.perturbed_apply, inclusion_graphLift, action_graphLift,
    add_sub_cancel_right]

namespace BoundedInverse

variable (C : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
variable (R : BoundedInverse (FormPerturbation.addBounded C (-B)))

theorem perturbed_equation (f : H) :
    C ⟨R.map f, R.mem_domain f⟩ = f + B (R.map f) := by
  have h := R.apply_map f
  change C ⟨R.map f, R.mem_domain f⟩ + -B (R.map f) = f at h
  rw [← sub_eq_add_neg] at h
  exact sub_eq_iff_eq_add.mp h

/-- The same two-sided inverse with values in the graph of C. -/
def perturbedGraphInverse : H →L[𝕜] GraphNorm.space C :=
  graphLift C B R.map R.mem_domain (R.perturbed_equation C B)

@[simp] theorem inclusion_perturbedGraphInverse (f : H) :
    GraphNorm.inclusion C (R.perturbedGraphInverse C B f) = R.map f := rfl

@[simp] theorem perturbed_apply_inverse (f : H) :
    GraphNorm.perturbed C B (R.perturbedGraphInverse C B f) = f :=
  perturbed_graphLift C B R.map R.mem_domain (R.perturbed_equation C B) f

@[simp] theorem perturbed_inverse_apply (u : GraphNorm.space C) :
    R.perturbedGraphInverse C B (GraphNorm.perturbed C B u) = u := by
  apply GraphNorm.inclusion_injective C
  rw [inclusion_perturbedGraphInverse]
  have h := R.map_apply ⟨GraphNorm.inclusion C u, GraphNorm.inclusion_mem_domain C u⟩
  simpa only [FormPerturbation.addBounded_apply, neg_apply, GraphNorm.action_eq,
    ← sub_eq_add_neg, GraphNorm.perturbed_apply] using h

theorem perturbedGraphInverse_opNorm_le (hB : ‖B‖ ≤ 25) {L : ℝ}
    (hL : 1 ≤ L) (hR : ‖R.map‖ ≤ L) : ‖R.perturbedGraphInverse C B‖ ≤ 27 * L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro f
  apply GraphNorm.inverse_graph_bound C B hB hL _ f (R.perturbed_apply_inverse C B f)
  rw [inclusion_perturbedGraphInverse]
  exact (R.map.le_opNorm f).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg f))

theorem perturbed_condition_bound (hB : ‖B‖ ≤ 25) {L : ℝ}
    (hL : 1 ≤ L) (hR : ‖R.map‖ ≤ L) :
    ‖GraphNorm.perturbed C B‖ * ‖R.perturbedGraphInverse C B‖ ≤ 702 * L := by
  apply GraphNorm.condition_bound C B hB hL _ (R.perturbed_apply_inverse C B)
  intro f
  rw [inclusion_perturbedGraphInverse]
  exact (R.map.le_opNorm f).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg f))

/-- Recover the L² field error directly from a computed source residual. -/
theorem perturbed_residual_bound {L : ℝ} (hR : ‖R.map‖ ≤ L)
    (u : GraphNorm.space C) (f : H) :
    ‖GraphNorm.inclusion C u - R.map f‖ ≤ L * ‖GraphNorm.perturbed C B u - f‖ := by
  have h := congrArg (GraphNorm.inclusion C) (R.perturbed_inverse_apply C B u)
  rw [inclusion_perturbedGraphInverse] at h
  calc
    ‖GraphNorm.inclusion C u - R.map f‖ =
        ‖R.map (GraphNorm.perturbed C B u - f)‖ := by rw [map_sub, h]
    _ ≤ ‖R.map‖ * ‖GraphNorm.perturbed C B u - f‖ := R.map.le_opNorm _
    _ ≤ L * ‖GraphNorm.perturbed C B u - f‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)

end BoundedInverse

end Maxwell.Continuum.SelfAdjointResolvent
