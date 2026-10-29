import Maxwell.Continuum.FiberNormalizationStar
import Maxwell.Continuum.FiberReflectionGraph

/-! Coordinatewise conjugation of the actual infinite-alias Maxwell graph. -/

noncomputable section
namespace Maxwell.Continuum.FiberNormalization

set_option backward.isDefEq.respectTransparency false

open FreeFiber

theorem block_star (p : Momentum) (E : ℂ) (v : Polarization) :
    star (block p E v) = block (star p) (star E) (star v) := by
  apply PiLp.ext
  intro j
  change star (block p E v j) = block (star p) (star E) (star v) j
  simp only [FiberReflection.block_coordinate, momentumSquare, bilinearDot]
  simp only [star_sub, star_mul, star_pow, star_sum]
  simp only [Pi.star_apply, polarization_star_apply]
  simp only [mul_comm]

theorem aliasMomentum_star (q : Momentum) (ν : Alias) :
    aliasMomentum (star q) ν = star (aliasMomentum q ν) := by
  funext j
  simp [aliasMomentum, star_add, star_mul, mul_comm]

theorem potential_star (v : FiberSpace) : star (potential v) = potential (star v) := by
  apply lp.ext
  funext ν
  change star (potential v ν) = potential (star v) ν
  simp only [potential_apply, star_sum, star_smul, star_add]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rfl

theorem free_graph_star (q : Momentum) (E : ℂ) (u v : FiberSpace)
    (h : (u, v) ∈ (FreeFiber.operator q E).graph) :
    (star u, star v) ∈ (FreeFiber.operator (star q) (star E)).graph := by
  rw [operator_graph_iff] at h ⊢
  intro ν
  rw [aliasMomentum_star]
  change block (star (aliasMomentum q ν)) (star E) (star (u ν)) = star (v ν)
  rw [← block_star, h ν]

theorem material_graph_star (q : Momentum) (E : ℂ) (ρ : ℝ) (u v : FiberSpace)
    (h : (u, v) ∈ (materialFiber q E ρ).graph) :
    (star u, star v) ∈ (materialFiber (star q) (star E) ρ).graph := by
  have hfree := free_graph_star q E u (v + (ρ : ℂ) • potential u)
    ((Bloch.materialFiber_graph_iff q E ρ u v).mp h)
  apply (Bloch.materialFiber_graph_iff _ _ _ _ _).mpr
  simpa only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, potential_star] using hfree

theorem star_realMomentum (q : Fin 3 → ℝ) : star (realMomentum q) = realMomentum q := by
  funext j
  simp [realMomentum]

#print axioms material_graph_star

end Maxwell.Continuum.FiberNormalization
