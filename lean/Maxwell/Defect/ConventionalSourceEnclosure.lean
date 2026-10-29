import Maxwell.Defect.CoherentSourceEnclosure
import Maxwell.Defect.EdgeSourceReference
import Maxwell.Spectral.ConventionalRational

/-! The actual conventional TRIM eigenvector supplies an executable
rational enclosure sequence for its physical coherent-cube source. -/
namespace Maxwell.Defect.ScalarDefect
open Spectral Spectral.Lattice Spectral.Bloch Spectral.PeriodicYee
open Spectral.ConventionalRational EdgeSourceEnclosure Filter Topology Module.End

/-- The concrete checker ordering is undone by the proved base-20 index. -/
def conventionalVectorSequence (material : PeriodicYee.Cell20 → ℚ) (k : Site)
    (left right : ℚ) (reference : Fin 24000 → ℚ)
    (h : ∀ stage, ∃ code, check (finiteFiber material k) left right reference
      (referenceBound reference) (accuracy stage) code = true)
    (stage : ℕ) (r : Edge20) : ℚ :=
  sequence (finiteFiber material k) left right reference (referenceBound reference)
    h stage (electricIndex r)

def conventionalCoherentSequence (L : ℕ) (material : PeriodicYee.Cell20 → ℚ) (k : Site)
    (left right : ℚ) (reference : Fin 24000 → ℚ)
    (h : ∀ stage, ∃ code, check (finiteFiber material k) left right reference
      (referenceBound reference) (accuracy stage) code = true) :
    ℕ → Fin (edges (cube L)).card → ℚ :=
  coherentSourceSequence L k (conventionalVectorSequence material k left right reference h)

theorem conventionalVectorSequence_coordinate_error
    (material : PeriodicYee.Cell20 → ℚ) (k : Site) (left right : ℚ) (reference : Fin 24000 → ℚ)
    (h : ∀ stage, ∃ code, check (finiteFiber material k) left right reference
      (referenceBound reference) (accuracy stage) code = true)
    (φ : EuclideanSpace ℂ Edge20)
    (herror : ∀ stage, ‖finiteRealVector φ - rationalVector
      (sequence (finiteFiber material k) left right reference (referenceBound reference) h stage)‖ ≤
        (accuracy stage : ℝ)) :
    ∀ stage r, |(φ r).re -
      (conventionalVectorSequence material k left right reference h stage r : ℝ)| ≤
        (accuracy stage : ℝ) := by
  intro stage r
  have hh := (PiLp.norm_apply_le (finiteRealVector φ - rationalVector
    (sequence (finiteFiber material k) left right reference (referenceBound reference) h stage))
      (electricIndex r)).trans (herror stage)
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, finiteRealVector, realCoordinatePart_apply,
    complexCoordinates_apply, Equiv.symm_apply_apply, rationalVector,
    conventionalVectorSequence] using hh

set_option maxHeartbeats 800000 in
/-- All rational source data are constructed from the same actual unit
simple edge vector. The real vector occurs only in correctness proofs. -/
theorem exists_conventional_coherent_sequence (L : ℕ) (material : PeriodicYee.Cell20 → ℚ) (k : Site)
    (φ : EuclideanSpace ℂ Edge20) (μ : ℝ)
    (hφ : ‖φ‖ = 1) (hreal : ∀ r, (φ r).im = 0)
    (heigen : Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
      (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)) φ =
        (μ : ℂ) • φ)
    (hdim : Module.finrank ℂ (eigenspace
      (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)).toEuclideanLin
        (μ : ℂ)) = 1) :
    ∃ (left right : ℚ) (reference : Fin 24000 → ℚ)
      (h : ∀ stage, ∃ code, check (finiteFiber material k) left right reference
        (referenceBound reference) (accuracy stage) code = true),
      (left : ℝ) < μ ∧ μ < (right : ℝ) ∧
      (∀ ν ∈ spectrum ℝ (rationalOperator (finiteFiber material k)),
        ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ) ∧
      (∀ stage,
        ‖realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
          (momentumTorus (fun j => Real.pi * (k j : ℝ))))) -
          rationalVector (conventionalCoherentSequence L material k left right reference h stage)‖ ≤
            (coherentSourceError L stage : ℝ)) ∧
      Tendsto (fun stage => (coherentSourceError L stage : ℝ)) atTop (𝓝 0) ∧
      0 < coherentSourceBound L k (conventionalVectorSequence material k left right reference h) ∧
      ‖realCoordinatePart (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n
        (momentumTorus (fun j => Real.pi * (k j : ℝ)))))‖ ≤
          (coherentSourceBound L k
            (conventionalVectorSequence material k left right reference h) : ℝ) := by
  have hφ0 : φ ≠ 0 := by intro hh; simp [hh] at hφ
  have hn : ‖finiteRealVector φ‖ = 1 := (finiteRealVector_norm φ hreal).trans hφ
  have he := finiteRealVector_eigen material k φ μ hreal heigen
  have hs := finiteRealVector_simple material k φ μ hφ0 hreal heigen hdim
  obtain ⟨left, right, reference, h, hl, hr, hi, _, he, _⟩ :=
    exists_certified_sequence (finiteFiber material k) (finiteFiber_symmetric material k)
      (finiteRealVector φ) μ hn he hs
  have hec := conventionalVectorSequence_coordinate_error material k left right reference h φ he
  exact ⟨left, right, reference, h, hl, hr, hi,
    coherentSourceSequence_error L k φ hφ _ hec,
    coherentSourceError_tendsto L, coherentSourceBound_pos L k _,
    coherentSource_norm_le_bound L k φ hφ _ hec⟩

end Maxwell.Defect.ScalarDefect
