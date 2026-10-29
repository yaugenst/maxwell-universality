import Maxwell.Defect.ConventionalSourceEnclosure
import Maxwell.Defect.EdgeEnergyEnclosure

/-! The physical coherent source and edge energy have executable rational
enclosures certified against the same conventional fiber and isolating
interval. This supplies the finite data used by inverse and numerator budgets. -/
namespace Maxwell.Defect.ScalarDefect
open Spectral Spectral.Lattice Spectral.Bloch Spectral.PeriodicYee
open Spectral.ConventionalRational EdgeSourceEnclosure Filter Topology Module.End

set_option maxHeartbeats 800000 in
theorem exists_conventional_coherent_energy_sequences
    (L : ℕ) (material : PeriodicYee.Cell20 → ℚ) (k : Site)
    (φ : EuclideanSpace ℂ Edge20) (μ : ℝ)
    (hφ : ‖φ‖ = 1) (hreal : ∀ r, (φ r).im = 0)
    (heigen : Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
      (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)) φ =
        (μ : ℂ) • φ)
    (hdim : Module.finrank ℂ (eigenspace
      (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)).toEuclideanLin
        (μ : ℂ)) = 1) :
    ∃ (left right : ℚ) (reference : Fin 24000 → ℚ)
      (hs : ∀ stage, ∃ code, check (finiteFiber material k) left right reference
        (referenceBound reference) (accuracy stage) code = true)
      (he : ∀ stage, ∃ code, EdgeEnergyEnclosure.check (finiteFiber material k) left right
        (accuracy stage) code = true),
      (left : ℝ) < μ ∧ μ < (right : ℝ) ∧
      (∀ stage,
        ‖realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
          (momentumTorus (fun j => Real.pi * (k j : ℝ))))) -
          rationalVector (conventionalCoherentSequence L material k left right reference hs stage)‖ ≤
            (coherentSourceError L stage : ℝ)) ∧
      Tendsto (fun stage => (coherentSourceError L stage : ℝ)) atTop (𝓝 0) ∧
      0 < coherentSourceBound L k (conventionalVectorSequence material k left right reference hs) ∧
      ‖realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
        (momentumTorus (fun j => Real.pi * (k j : ℝ)))))‖ ≤
          (coherentSourceBound L k
            (conventionalVectorSequence material k left right reference hs) : ℝ) ∧
      (∀ stage,
        ((EdgeEnergyEnclosure.sequence (finiteFiber material k) left right he stage).1 : ℝ) ≤ μ ∧
        μ ≤ ((EdgeEnergyEnclosure.sequence (finiteFiber material k) left right he stage).2 : ℝ)) ∧
      Tendsto (fun stage =>
        ((EdgeEnergyEnclosure.sequence (finiteFiber material k) left right he stage).1 : ℝ)) atTop (𝓝 μ) ∧
      Tendsto (fun stage =>
        ((EdgeEnergyEnclosure.sequence (finiteFiber material k) left right he stage).2 : ℝ)) atTop (𝓝 μ) := by
  obtain ⟨left, right, reference, hs, hl, hr, hi, hsource, hsourceLimit, hboundPos, hbound⟩ :=
    exists_conventional_coherent_sequence L material k φ μ hφ hreal heigen hdim
  have hφ0 : φ ≠ 0 := by intro hh; simp [hh] at hφ
  have hn : ‖finiteRealVector φ‖ = 1 := (finiteRealVector_norm φ hreal).trans hφ
  have heig := finiteRealVector_eigen material k φ μ hreal heigen
  have hsimple := finiteRealVector_simple material k φ μ hφ0 hreal heigen hdim
  let he := EdgeEnergyEnclosure.sequence_terminates (finiteFiber material k)
    (finiteFiber_symmetric material k) left right (finiteRealVector φ) μ hn heig hsimple hl hr
  obtain ⟨hb, hlow, hupp⟩ := EdgeEnergyEnclosure.certified_sequence (finiteFiber material k)
    left right he μ hi
  exact ⟨left, right, reference, hs, he, hl, hr, hsource, hsourceLimit, hboundPos, hbound,
    fun stage => ⟨(hb stage).1, (hb stage).2.1⟩, hlow, hupp⟩

end Maxwell.Defect.ScalarDefect
