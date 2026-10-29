import Maxwell.Continuum.FiberReflection
import Maxwell.Continuum.BlochPeriodicGraph

/-! Coordinate reflection of the actual infinite material fiber, preserving
the full maximal graph and nonzero kernel vectors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberReflection

open FreeFiber

theorem material_graph_reflect (j : Fin 3) (q : Momentum) (E : ℂ) (ρ : ℝ)
    (u v : FiberSpace) (h : (u, v) ∈ (materialFiber q E ρ).graph) :
    (fiber j u, fiber j v) ∈ (materialFiber (momentum j q) E ρ).graph := by
  have hg := free_graph_reflect j q E u (v + (ρ : ℂ) • potential u)
    ((Bloch.materialFiber_graph_iff q E ρ u v).mp h)
  apply (Bloch.materialFiber_graph_iff _ _ _ _ _).mpr
  have heq : fiber j (v + (ρ : ℂ) • potential u) =
      fiber j v + (ρ : ℂ) • potential (fiber j u) := by
    rw [map_add, map_smul]
    exact congrArg (fun w : FiberSpace => fiber j v + (ρ : ℂ) • w)
      (potential_reflect j u).symm
  exact heq ▸ hg

theorem material_graph_reflect_iff (j : Fin 3) (q : Momentum) (E : ℂ) (ρ : ℝ)
    (u v : FiberSpace) :
    (fiber j u, fiber j v) ∈ (materialFiber (momentum j q) E ρ).graph ↔
      (u, v) ∈ (materialFiber q E ρ).graph := by
  constructor
  · intro h
    have hh := material_graph_reflect j (momentum j q) E ρ (fiber j u) (fiber j v) h
    have hp : (fiber j (fiber j u), fiber j (fiber j v)) = (u, v) :=
      congrArg₂ Prod.mk (fiber_involutive j u) (fiber_involutive j v)
    have hh' : (u, v) ∈ (materialFiber (momentum j (momentum j q)) E ρ).graph := hp ▸ hh
    exact (congrArg (fun p : Momentum => (u, v) ∈ (materialFiber p E ρ).graph)
      (momentum_involutive j q)).mp hh'
  · exact material_graph_reflect j q E ρ u v

/-- A literal nonzero fiber eigenvector exists at a reflected momentum exactly
when one exists at the original momentum. -/
theorem nonzero_kernel_reflect_iff (j : Fin 3) (q : Momentum) (E : ℂ) (ρ : ℝ) :
    (∃ u : FiberSpace, u ≠ 0 ∧ (u, 0) ∈ (materialFiber (momentum j q) E ρ).graph) ↔
      ∃ u : FiberSpace, u ≠ 0 ∧ (u, 0) ∈ (materialFiber q E ρ).graph := by
  have transfer (p : Momentum)
      (h : ∃ u : FiberSpace, u ≠ 0 ∧ (u, 0) ∈ (materialFiber p E ρ).graph) :
      ∃ u : FiberSpace, u ≠ 0 ∧ (u, 0) ∈ (materialFiber (momentum j p) E ρ).graph := by
    obtain ⟨u, hu, hgraph⟩ := h
    refine ⟨fiber j u, ?_, ?_⟩
    · intro hzero
      apply hu
      apply (fiber j).injective
      exact hzero.trans (fiber j).map_zero.symm
    · simpa only [map_zero] using material_graph_reflect j p E ρ u 0 hgraph
  constructor
  · intro h
    exact (congrArg (fun p : Momentum => ∃ u : FiberSpace, u ≠ 0 ∧
      (u, 0) ∈ (materialFiber p E ρ).graph) (momentum_involutive j q)).mp
        (transfer (momentum j q) h)
  · exact transfer q

theorem momentum_scaled (j : Fin 3) (t : Momentum) :
    momentum j (scaledMomentum t) = scaledMomentum (momentum j t) := by
  funext k
  change coordinateSign j k * ((backgroundAmplitude : ℂ) * t k) =
    (backgroundAmplitude : ℂ) * (coordinateSign j k * t k)
  ring

theorem momentum_coordinate_norm (j : Fin 3) (t : Momentum) (k : Fin 3) :
    ‖momentum j t k‖ = ‖t k‖ := by
  change ‖coordinateSign j k * t k‖ = ‖t k‖
  rw [norm_mul, coordinateSign_norm, one_mul]

theorem actual_kernel_reflect_iff (j : Fin 3) (t : Momentum) (e : ℂ) :
    (∃ u : FiberSpace, u ≠ 0 ∧
      (u, 0) ∈ (materialFiber (scaledMomentum (momentum j t))
        (totalEnergy e) backgroundAmplitude).graph) ↔
    ∃ u : FiberSpace, u ≠ 0 ∧
      (u, 0) ∈ (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).graph := by
  rw [← momentum_scaled]
  exact nonzero_kernel_reflect_iff j (scaledMomentum t) (totalEnergy e) backgroundAmplitude

end Maxwell.Continuum.FiberReflection
