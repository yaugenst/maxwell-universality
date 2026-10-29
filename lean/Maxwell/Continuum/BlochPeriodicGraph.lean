import Maxwell.Continuum.BlochFreeGraph

/-! The physical periodic Maxwell equation has exactly the full maximal
Bloch-fiber graph constructed in the periodic spectral analysis. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

theorem materialFiber_graph_iff (q : FreeFiber.Momentum) (E : ℂ) (ρ : ℝ)
    (u v : FreeFiber.FiberSpace) :
    (u, v) ∈ (FreeFiber.materialFiber q E ρ).graph ↔
      (u, v + (ρ : ℂ) • FreeFiber.potential u) ∈ (FreeFiber.operator q E).graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  change (∃ x : (FreeFiber.operator q E).domain, (x : FreeFiber.FiberSpace) = u ∧
    FreeFiber.materialFiber q E ρ x = v) ↔
      ∃ x : (FreeFiber.operator q E).domain, (x : FreeFiber.FiberSpace) = u ∧
        FreeFiber.operator q E x = v + (ρ : ℂ) • FreeFiber.potential u
  constructor
  · rintro ⟨x, hx, hv⟩
    refine ⟨x, hx, ?_⟩
    rw [FreeFiber.materialFiber_apply] at hv
    rw [← hx]
    exact sub_eq_iff_eq_add.mp hv
  · rintro ⟨x, hx, hv⟩
    refine ⟨x, hx, ?_⟩
    rw [FreeFiber.materialFiber_apply, hv, hx, add_sub_cancel_right]

/-- The physical periodic scalar material acts on the literal continuum equation. -/
def WeakPeriodicEquation (u v : FieldL2) : Prop :=
  curlDistribution (curlDistribution (fieldDistribution u)) -
    fieldDistribution (PeriodicMaterial.dielectric.multiplier u) = fieldDistribution v

theorem weakPeriodicEquation_iff_free (u v : FieldL2) :
    WeakPeriodicEquation u v ↔
      WeakFreeEquation 7 u (v + (FreeFiber.backgroundAmplitude : ℂ) • physicalPotential u) := by
  unfold WeakPeriodicEquation WeakFreeEquation
  rw [periodicMultiplier_eq]
  simp only [map_add, map_smul]
  rw [sub_add_eq_sub_sub]
  exact sub_eq_iff_eq_add

theorem unitary_shiftedSource_ae (u v : FieldL2) :
    unitary (v + (FreeFiber.backgroundAmplitude : ℂ) • physicalPotential u) =ᵐ[quasiMeasure]
      (fun q => unitary v q + (FreeFiber.backgroundAmplitude : ℂ) •
        FreeFiber.potential (unitary u q)) := by
  rw [map_add, map_smul, unitary_physicalPotential]
  filter_upwards [Lp.coeFn_add (unitary v)
      ((FreeFiber.backgroundAmplitude : ℂ) • potentialL2 (unitary u)),
    Lp.coeFn_smul (FreeFiber.backgroundAmplitude : ℂ) (potentialL2 (unitary u)),
    potentialL2_ae (unitary u)] with q ha hs hp
  rw [ha]
  simp only [Pi.add_apply, hs, Pi.smul_apply, hp]

/-- Exact direct-integral identity for the actual scalar periodic Maxwell medium.
Both sides use their full L² maximal graph and the constructed unitary transform. -/
theorem weakPeriodicEquation_iff_fiber_graph (u v : FieldL2) :
    WeakPeriodicEquation u v ↔
      ∀ᵐ q ∂quasiMeasure,
        (unitary u q, unitary v q) ∈
          (FreeFiber.materialFiber (quasiMomentum q) 7 FreeFiber.backgroundAmplitude).graph := by
  rw [weakPeriodicEquation_iff_free, weakFreeEquation_iff_fiber_graph]
  constructor
  · intro h
    filter_upwards [h, unitary_shiftedSource_ae u v] with q hq hs
    rw [materialFiber_graph_iff]
    rwa [hs] at hq
  · intro h
    filter_upwards [h, unitary_shiftedSource_ae u v] with q hq hs
    rw [hs]
    exact (materialFiber_graph_iff _ _ _ _ _).mp hq

end Maxwell.Continuum.Bloch
