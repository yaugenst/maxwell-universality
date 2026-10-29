import Maxwell.Continuum.PeriodicBandPhysicalGap
import Maxwell.Continuum.FiberEnergy

/-! Energy shifts of the actual full maximal-domain material graph.
Momentum remains fixed; no common domain across different momenta is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FreeFiber

open ClusterComplement

theorem inverse_scaled_on_kernel (q : Momentum) (E F : ℂ) (ρ : ℝ)
    (R : SelfAdjointResolvent.BoundedInverse (materialFiber q E ρ))
    (u : FiberSpace) (hu : (u, 0) ∈ (materialFiber q F ρ).graph) :
    (E - F) • R.map u = -u := by
  have hs := material_graph_energy_shift q F E ρ u 0 hu
  rw [LinearPMap.mem_graph_iff] at hs
  obtain ⟨w, hw, hMw⟩ := hs
  have hR := R.map_apply w
  rw [hMw, zero_add, map_smul] at hR
  rw [show F - E = -(E - F) by ring, neg_smul] at hR
  have hw' : w.val = u := hw
  rw [hw'] at hR
  exact neg_eq_iff_eq_neg.mp hR

end Maxwell.Continuum.FreeFiber
