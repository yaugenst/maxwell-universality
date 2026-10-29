import Maxwell.Defect.EdgeSourceEnclosure
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! Rational isolation and orientation data for the executable finite-matrix
source enclosure. These data follow from the actual finite eigenpair; they
are not additional hypotheses of the source construction. -/

namespace Maxwell.Defect.EdgeSourceEnclosure

open InnerProductSpace Module.End Filter Topology

variable {n : ℕ}

/-- A finite matrix spectrum admits a strict rational isolating interval
around any selected spectral value. Multiplicity does not affect isolation. -/
theorem exists_rational_isolating_interval (T : Matrix (Fin n) (Fin n) ℚ) (μ : ℝ) :
    ∃ left right : ℚ, (left : ℝ) < μ ∧ μ < (right : ℝ) ∧
      ∀ ν ∈ spectrum ℝ (rationalOperator T),
        ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ := by
  have hfinite : (spectrum ℝ (rationalOperator T)).Finite := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact Module.End.finite_spectrum _
  let other := spectrum ℝ (rationalOperator T) \ {μ}
  have hopen : IsOpen otherᶜ := (hfinite.sdiff).isClosed.isOpen_compl
  have hmem : μ ∈ otherᶜ := by simp [other]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen μ hmem
  obtain ⟨left, hlower, hleft⟩ := exists_rat_btwn (show μ - r < μ by linarith)
  obtain ⟨right, hright, hupper⟩ := exists_rat_btwn (show μ < μ + r by linarith)
  refine ⟨left, right, hleft, hright, ?_⟩
  intro ν hν hinterval
  have hnear : ν ∈ Metric.ball μ r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hinterval.1, hinterval.2]
  have hnot := hball hnear
  by_contra hne
  exact hnot ⟨hν, by simpa using hne⟩

/-- Every actual unit real vector has a rational reference with positive
inner product, fixing the sign of its one-dimensional eigenspace. -/
theorem exists_rational_positive_reference (u : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) :
    ∃ reference : Fin n → ℚ, 0 < inner ℝ u (rationalVector reference) := by
  obtain ⟨q, hq⟩ := exists_rational_vector_sequence u
  have hlim : Tendsto (fun k => inner ℝ u (rationalVector (q k))) atTop (𝓝 1) := by
    simpa only [rationalVector, real_inner_self_eq_norm_sq, hu, one_pow] using
      ((tendsto_const_nhds (x := u)).inner (𝕜 := ℝ) hq)
  obtain ⟨k, hk⟩ := (hlim.eventually_const_lt (by norm_num : (0 : ℝ) < 1)).exists
  exact ⟨q k, hk⟩

/-- The actual unit simple eigenpair supplies every fixed rational input
needed by the executable search. Execution of `sequence` reads the matrix,
interval, reference, and precision, with its termination proof erased. -/
theorem exists_certified_sequence (T : Matrix (Fin n) (Fin n) ℚ) (hT : T.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (hu : ‖u‖ = 1) (hTu : rationalOperator T u = μ • u)
    (hsimple : Module.finrank ℝ (eigenspace (rationalOperator T).toLinearMap μ) = 1) :
    ∃ (left right : ℚ) (reference : Fin n → ℚ)
      (h : ∀ k, ∃ code,
        check T left right reference (referenceBound reference) (accuracy k) code = true),
      (left : ℝ) < μ ∧ μ < (right : ℝ) ∧
      (∀ ν ∈ spectrum ℝ (rationalOperator T),
        ν ∈ Set.Icc (left : ℝ) (right : ℝ) → ν = μ) ∧
      0 < inner ℝ u (rationalVector reference) ∧
      (∀ k, ‖u - rationalVector
        (sequence T left right reference (referenceBound reference) h k)‖ ≤ (accuracy k : ℝ)) ∧
      Tendsto (fun k => (accuracy k : ℝ)) atTop (𝓝 0) := by
  obtain ⟨left, right, hleft, hright, hisolate⟩ := exists_rational_isolating_interval T μ
  obtain ⟨reference, horient⟩ := exists_rational_positive_reference u hu
  let h := sequence_terminates T hT left right reference u μ hu hTu hsimple hleft hright horient
  exact ⟨left, right, reference, h, hleft, hright, hisolate, horient,
    certified_sequence T hT left right reference u μ hu hTu hsimple
      hleft hright hisolate horient⟩

end Maxwell.Defect.EdgeSourceEnclosure
