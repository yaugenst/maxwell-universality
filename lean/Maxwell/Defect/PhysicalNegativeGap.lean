import Maxwell.Green.PhysicalEdge

/-! A fixed gap below every sufficiently small shifted physical edge.
The interval exclusion is derived from the actual local eigenbranch and
the full real far exclusion, so the negative gap is a conclusion. -/
namespace Maxwell.Defect.PhysicalLimit

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green Maxwell.Green.PhysicalAnalytic

noncomputable section

/-- Uniform exclusion of an interval below the edge gives a fixed lower
spectral gap for every shift in its upper half. -/
theorem negative_gap_of_interval_exclusion {ι : Type*} (bands : ι → Set ℝ)
    (edge δ : ℝ)
    (hexclude : ∀ η : ℝ, 0 < η → η < δ → ∀ t, edge - η ∉ bands t)
    (ξ : ℝ) (hξ : 0 < ξ) (hξδ : ξ < δ / 2) :
    (∀ t, edge - ξ ∉ bands t) ∧
      ∀ t, ∀ s ∈ bands t, s ≤ edge - ξ - δ / 2 ∨ edge - ξ ≤ s := by
  refine ⟨hexclude ξ hξ (by linarith), ?_⟩
  intro t s hs
  by_cases hedge : edge ≤ s
  · exact Or.inr (by linarith)
  · left
    have hdist : δ ≤ edge - s := by
      by_contra! hdist
      have hnot := hexclude (edge - s) (by linarith) hdist t
      apply hnot
      simpa only [sub_sub_cancel] using hs
    linarith

/-- The actual physical branch has a uniform negative spectral gap near
the edge. Both the shifted resolvent exclusion and the fixed gap follow
from the same finite spectral data; neither is supplied as an estimate. -/
theorem exists_physical_negative_gap {material : Cell20 → ℝ} {edge : ℝ}
    {θ : RealTorusCoordinates} (S : PhysicalSimpleEdgeData material edge θ) :
    ∃ δ g : ℝ, 0 < δ ∧ 0 < g ∧ ∀ ξ : ℝ, 0 < ξ → ξ < δ →
      (∀ t : Torus, edge - ξ ∉ spectrum ℝ
        (torusElectric (PeriodicYee.edgeAverage material) t)) ∧
      ∀ t : Torus, ∀ s ∈ spectrum ℝ
        (torusElectric (PeriodicYee.edgeAverage material) t),
        s ≤ edge - ξ - g ∨ edge - ξ ≤ s := by
  obtain ⟨δ, hδ, hexclude⟩ := S.exists_real_gap
  refine ⟨δ / 2, δ / 2, by positivity, by positivity, ?_⟩
  exact negative_gap_of_interval_exclusion
    (fun t => spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t))
    edge δ hexclude

end
end Maxwell.Defect.PhysicalLimit
