import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Maximal block multiplication on a Hilbert sum

The domain is defined by square summability of the actual block images. It
is not replaced by a momentum-independent Sobolev domain. Uniformly bounded
block inverses give an inverse into this full maximal domain.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev HilbertSum (ι E : Type*) [NormedAddCommGroup E] := lp (fun _ : ι => E) 2

/-- The maximal domain of a family of continuous finite block operators. -/
def maximalDomain (B : ι → E →L[ℂ] E) : Submodule ℂ (HilbertSum ι E) where
  carrier := {u | Memℓp (fun i => B i (u i)) 2}
  zero_mem' := by
    change Memℓp (fun i => B i 0) 2
    simpa only [map_zero] using (zero_mem_ℓp' (E := fun _ : ι => E) (p := 2))
  add_mem' := by
    intro u v hu hv
    change Memℓp (fun i => B i (u i + v i)) 2
    simp only [map_add]
    convert hu.add hv using 1
  smul_mem' := by
    intro c u hu
    change Memℓp (fun i => B i (c • u i)) 2
    simp only [map_smul]
    convert hu.const_smul c using 1

@[simp]
theorem mem_maximalDomain (B : ι → E →L[ℂ] E) (u : HilbertSum ι E) :
    u ∈ maximalDomain B ↔ Memℓp (fun i => B i (u i)) 2 := Iff.rfl

/-- Actual block multiplication with the full maximal domain. -/
def maximalOperator (B : ι → E →L[ℂ] E) : HilbertSum ι E →ₗ.[ℂ] HilbertSum ι E where
  domain := maximalDomain B
  toFun :=
    { toFun := fun u => ⟨fun i => B i (u.val i), u.property⟩
      map_add' := by intro u v; apply Subtype.ext; funext i; exact (B i).map_add _ _
      map_smul' := by intro c u; apply Subtype.ext; funext i; exact (B i).map_smul c _ }

@[simp]
theorem maximalOperator_apply (B : ι → E →L[ℂ] E) (u : (maximalOperator B).domain)
    (i : ι) : maximalOperator B u i = B i (u.val i) := rfl

/-- Coordinate identities characterize the graph, including domain membership. -/
theorem maximalOperator_graph_iff (B : ι → E →L[ℂ] E) (u v : HilbertSum ι E) :
    (u, v) ∈ (maximalOperator B).graph ↔ ∀ i, B i (u i) = v i := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨w, hw, hBw⟩ i
    change w.val = u at hw
    rw [← hw]
    exact congrArg (fun z : HilbertSum ι E => z i) hBw
  · intro h
    have hu : u ∈ maximalDomain B := by
      change Memℓp (fun i => B i (u i)) 2
      simpa only [funext h] using lp.memℓp v
    exact ⟨⟨u, hu⟩, rfl, Subtype.ext (funext h)⟩

/-- Maximal block multiplication is closed, with no uniform bound on the blocks. -/
theorem maximalOperator_isClosed (B : ι → E →L[ℂ] E) :
    (maximalOperator B).IsClosed := by
  have hgraph : ((maximalOperator B).graph : Set (HilbertSum ι E × HilbertSum ι E)) =
      ⋂ i, {z | B i (z.1 i) = z.2 i} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact maximalOperator_graph_iff B z.1 z.2
  rw [LinearPMap.IsClosed, hgraph]
  apply isClosed_iInter
  intro i
  exact isClosed_eq
    ((B i).continuous.comp ((lp.evalCLM ℂ (fun _ : ι => E) 2 i).continuous.comp continuous_fst))
    ((lp.evalCLM ℂ (fun _ : ι => E) 2 i).continuous.comp continuous_snd)

/-- Pointwise application of a uniformly bounded family preserves square summability. -/
theorem boundedBlocks_memℓp (R : ι → E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ i, ‖R i‖ ≤ C) (u : HilbertSum ι E) :
    Memℓp (fun i => R i (u i)) 2 := by
  apply (lp.memℓp ((C : ℂ) • u)).mono'
  intro i
  calc
    ‖R i (u i)‖ ≤ ‖R i‖ * ‖u i‖ := (R i).le_opNorm _
    _ ≤ C * ‖u i‖ := mul_le_mul_of_nonneg_right (hR i) (norm_nonneg _)
    _ = ‖((C : ℂ) • u) i‖ := by
      change C * ‖u i‖ = ‖(C : ℂ) • u i‖
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

/-- The bounded operator assembled from a uniformly bounded block family. -/
def boundedBlocks (R : ι → E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ i, ‖R i‖ ≤ C) : HilbertSum ι E →L[ℂ] HilbertSum ι E :=
  lp.mapCLM 2 R hC hR

@[simp]
theorem boundedBlocks_apply (R : ι → E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ i, ‖R i‖ ≤ C) (u : HilbertSum ι E) (i : ι) :
    boundedBlocks R hC hR u i = R i (u i) := rfl

theorem boundedBlocks_norm_le (R : ι → E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ i, ‖R i‖ ≤ C) : ‖boundedBlocks R hC hR‖ ≤ C :=
  lp.norm_mapCLM_le 2 R hC hR

/-- A pointwise right inverse automatically takes values in the maximal domain. -/
theorem boundedBlocks_mem_maximalDomain (B R : ι → E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ i, ‖R i‖ ≤ C) (hBR : ∀ i x, B i (R i x) = x) (u : HilbertSum ι E) :
    boundedBlocks R hC hR u ∈ maximalDomain B := by
  change Memℓp (fun i => B i (R i (u i))) 2
  simpa only [hBR] using lp.memℓp u

theorem maximalOperator_boundedBlocks (B R : ι → E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ i, ‖R i‖ ≤ C) (hBR : ∀ i x, B i (R i x) = x) (u : HilbertSum ι E) :
    maximalOperator B ⟨boundedBlocks R hC hR u,
      boundedBlocks_mem_maximalDomain B R hC hR hBR u⟩ = u := by
  apply Subtype.ext
  funext i
  exact hBR i (u i)

theorem boundedBlocks_maximalOperator (B R : ι → E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hR : ∀ i, ‖R i‖ ≤ C) (hRB : ∀ i x, R i (B i x) = x)
    (u : (maximalOperator B).domain) :
    boundedBlocks R hC hR (maximalOperator B u) = u.val := by
  apply Subtype.ext
  funext i
  exact hRB i (u.val i)

end Maxwell.Continuum.FreeFiber
