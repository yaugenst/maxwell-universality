import Maxwell.Continuum.FormPerturbation
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Linarith

/-!
# The graph norm used by the continuum conditioning theorem

The domain norm is the Hilbert norm of the actual graph of C.  The map
C-B is bounded from this graph space to L²; C itself is never declared
bounded on all of L².  An L² inverse estimate then yields the constants
26, 27 and 702 in the paper.
-/

noncomputable section

namespace Maxwell.Continuum.GraphNorm

set_option backward.isDefEq.respectTransparency false

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

def space (C : H →ₗ.[𝕜] H) : Submodule 𝕜 (WithLp 2 (H × H)) :=
  C.graph.comap (WithLp.linearEquiv 2 𝕜 (H × H)).toLinearMap

theorem space_isClosed {C : H →ₗ.[𝕜] H} (hC : C.IsClosed) :
    IsClosed (space C : Set (WithLp 2 (H × H))) :=
  hC.preimage (WithLp.prodContinuousLinearEquiv 2 𝕜 H H).continuous

def inclusion (C : H →ₗ.[𝕜] H) : space C →L[𝕜] H :=
  (WithLp.fstL 2 𝕜 H H).comp (space C).subtypeL

def action (C : H →ₗ.[𝕜] H) : space C →L[𝕜] H :=
  (WithLp.sndL 2 𝕜 H H).comp (space C).subtypeL

theorem norm_sq (C : H →ₗ.[𝕜] H) (u : space C) :
    ‖u‖ ^ 2 = ‖inclusion C u‖ ^ 2 + ‖action C u‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.val

theorem inclusion_norm_le (C : H →ₗ.[𝕜] H) (u : space C) :
    ‖inclusion C u‖ ≤ ‖u‖ := WithLp.norm_fst_le (α := H) u.val

theorem action_norm_le (C : H →ₗ.[𝕜] H) (u : space C) :
    ‖action C u‖ ≤ ‖u‖ := WithLp.norm_snd_le (α := H) u.val

theorem norm_le_sum (C : H →ₗ.[𝕜] H) (u : space C) :
    ‖u‖ ≤ ‖inclusion C u‖ + ‖action C u‖ := by
  have hs := norm_sq C u
  have hp := mul_nonneg (norm_nonneg (inclusion C u)) (norm_nonneg (action C u))
  nlinarith [norm_nonneg u, norm_nonneg (inclusion C u), norm_nonneg (action C u)]

theorem inclusion_mem_domain (C : H →ₗ.[𝕜] H) (u : space C) :
    inclusion C u ∈ C.domain := by
  obtain ⟨v, hv, _⟩ := C.mem_graph_iff.mp u.property
  have hv' : (v : H) = inclusion C u := hv
  exact hv' ▸ v.property

theorem action_eq (C : H →ₗ.[𝕜] H) (u : space C) :
    C ⟨inclusion C u, inclusion_mem_domain C u⟩ = action C u := by
  obtain ⟨v, hv, ha⟩ := C.mem_graph_iff.mp u.property
  have he : (⟨inclusion C u, inclusion_mem_domain C u⟩ : C.domain) = v :=
    Subtype.ext hv.symm
  rw [he]
  exact ha

theorem inclusion_injective (C : H →ₗ.[𝕜] H) : Function.Injective (inclusion C) := by
  intro u v h
  have hd : (⟨inclusion C u, inclusion_mem_domain C u⟩ : C.domain) =
      ⟨inclusion C v, inclusion_mem_domain C v⟩ := Subtype.ext h
  have ha : action C u = action C v := by rw [← action_eq, ← action_eq, hd]
  apply Subtype.ext
  apply (WithLp.equiv 2 (H × H)).injective
  exact Prod.ext h ha

def perturbed (C : H →ₗ.[𝕜] H) (B : H →L[𝕜] H) : space C →L[𝕜] H :=
  action C - B.comp (inclusion C)

@[simp] theorem perturbed_apply (C : H →ₗ.[𝕜] H) (B : H →L[𝕜] H) (u : space C) :
    perturbed C B u = action C u - B (inclusion C u) := rfl

theorem perturbed_norm_le (C : H →ₗ.[𝕜] H) (B : H →L[𝕜] H) (hB : ‖B‖ ≤ 25) :
    ‖perturbed C B‖ ≤ 26 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  calc
    ‖perturbed C B u‖ ≤ ‖action C u‖ + ‖B (inclusion C u)‖ := norm_sub_le _ _
    _ ≤ ‖u‖ + 25 * ‖u‖ := add_le_add (action_norm_le C u)
      ((B.le_opNorm _).trans (mul_le_mul hB (inclusion_norm_le C u)
        (norm_nonneg _) (by norm_num)))
    _ = 26 * ‖u‖ := by ring

/-- The inverse estimate needed for the graph-norm condition number.
This consumes a genuine equation and an L² bound, not a norm on an
unbounded operator acting on all L² fields. -/
theorem inverse_graph_bound (C : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (hB : ‖B‖ ≤ 25) {L : ℝ} (hL : 1 ≤ L)
    (u : space C) (f : H) (heq : perturbed C B u = f)
    (hfield : ‖inclusion C u‖ ≤ L * ‖f‖) : ‖u‖ ≤ 27 * L * ‖f‖ := by
  have hA : action C u = f + B (inclusion C u) := by
    exact (sub_eq_iff_eq_add.mp heq)
  have hmaterial : ‖B (inclusion C u)‖ ≤ 25 * L * ‖f‖ := by
    calc
      ‖B (inclusion C u)‖ ≤ ‖B‖ * ‖inclusion C u‖ := B.le_opNorm _
      _ ≤ 25 * (L * ‖f‖) := mul_le_mul hB hfield (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  calc
    ‖u‖ ≤ ‖inclusion C u‖ + ‖action C u‖ := norm_le_sum C u
    _ ≤ L * ‖f‖ + (‖f‖ + 25 * L * ‖f‖) := by
      rw [hA]
      exact add_le_add hfield ((norm_add_le _ _).trans (add_le_add (le_refl _) hmaterial))
    _ ≤ 27 * L * ‖f‖ := by nlinarith [norm_nonneg f]

theorem condition_bound (C : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (hB : ‖B‖ ≤ 25) {L : ℝ} (hL : 1 ≤ L)
    (R : H →L[𝕜] space C)
    (heq : ∀ f, perturbed C B (R f) = f)
    (hfield : ∀ f, ‖inclusion C (R f)‖ ≤ L * ‖f‖) :
    ‖perturbed C B‖ * ‖R‖ ≤ 702 * L := by
  have hR : ‖R‖ ≤ 27 * L := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    intro f
    exact inverse_graph_bound C B hB hL (R f) f (heq f) (hfield f)
  calc
    ‖perturbed C B‖ * ‖R‖ ≤ 26 * (27 * L) :=
      mul_le_mul (perturbed_norm_le C B hB) hR (norm_nonneg R) (by norm_num)
    _ = 702 * L := by ring

end Maxwell.Continuum.GraphNorm
