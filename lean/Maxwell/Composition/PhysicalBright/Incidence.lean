import Maxwell.Composition.SourceMediator
import Maxwell.Composition.ModeBaseline
import Maxwell.Composition.PhysicalSymmetry

/-! The actual routed incidence pattern and its degree-three calibration
bound. This is a bound for the full Euclidean operator, not individual rows. -/
noncomputable section
namespace Maxwell.Composition.PhysicalBright
open Maxwell.Spectral Maxwell.Spectral.Lattice
open scoped BigOperators

section GenericIncidence
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Both orientations of a terminal/mediator incidence coupling. -/
def incidenceMatrix (G : SignedIncidence V E) (β : E → ℝ) :
    Matrix (V ⊕ E) (V ⊕ E) ℝ :=
  Matrix.fromBlocks 0 (G.coupling β) (G.coupling β).transpose 0

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem incidenceMatrix_symmetric (G : SignedIncidence V E) (β : E → ℝ) :
    (incidenceMatrix G β).IsSymm := by
  ext i j
  cases i <;> cases j <;> rfl

omit [DecidableEq E] in
theorem incidenceMatrix_row_bound (G : SignedIncidence V E) (β : E → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hβ : ∀ e, |β e| ≤ R)
    (hdegree : ∀ v, G.degree v ≤ 3) (i : V ⊕ E) :
    ∑ j, |incidenceMatrix G β i j| ≤ 3 * R := by
  cases i with
  | inl v =>
    simp only [Fintype.sum_sum_type, incidenceMatrix, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, abs_zero, Finset.sum_const_zero, zero_add]
    calc
      ∑ e, |G.coupling β v e| ≤ ∑ e, |G.incidence v e| * R := by
        apply Finset.sum_le_sum
        intro e _
        rw [SignedIncidence.coupling, abs_mul]
        exact mul_le_mul_of_nonneg_left (hβ e) (abs_nonneg _)
      _ = G.degree v * R := by rw [← Finset.sum_mul, G.incidence_row_sum]
      _ ≤ 3 * R := mul_le_mul_of_nonneg_right (hdegree v) hR
  | inr e =>
    simp only [Fintype.sum_sum_type, incidenceMatrix, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.zero_apply, abs_zero,
      Finset.sum_const_zero, add_zero]
    calc
      ∑ v, |G.coupling β v e| = (∑ v, |G.incidence v e|) * |β e| := by
        simp only [SignedIncidence.coupling, abs_mul, Finset.sum_mul]
      _ = 2 * |β e| := by rw [G.incidence_column_sum]
      _ ≤ 3 * R := by nlinarith [hβ e]

/-- All incidence calibration errors have norm at most three times the
single calibrated coupling error. -/
theorem incidenceMatrix_norm_le (G : SignedIncidence V E) (β : E → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hβ : ∀ e, |β e| ≤ R)
    (hdegree : ∀ v, G.degree v ≤ 3) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix G β)‖ ≤ 3 * R :=
  Maxwell.symmetric_matrix_toEuclideanCLM_norm_le _ _ (by positivity)
    (incidenceMatrix_symmetric G β) (incidenceMatrix_row_bound G β R hR hβ hdegree)

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem incidenceMatrix_add (G : SignedIncidence V E) (β γ : E → ℝ) :
    incidenceMatrix G (fun e => β e + γ e) = incidenceMatrix G β + incidenceMatrix G γ := by
  ext i j
  cases i <;> cases j <;> simp [incidenceMatrix, SignedIncidence.coupling, mul_add]

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem incidenceMatrix_neg (G : SignedIncidence V E) (β : E → ℝ) :
    incidenceMatrix G (fun e => -β e) = -incidenceMatrix G β := by
  ext i j
  cases i <;> cases j <;> simp [incidenceMatrix, SignedIncidence.coupling]

omit [Fintype V] in
/-- The target's diagonal and the actual incidence couplings are separated
exactly, retaining the mediator diagonal used by its Schur complement. -/
theorem targetMatrix_split (G : SignedIncidence V E) (α : ℝ)
    (β : E → ℝ) (diag : V → ℝ) :
    G.targetMatrix α β diag =
      Matrix.diagonal (fun i => G.targetMatrix α β diag i i) + incidenceMatrix G β := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases h : i = j <;> simp [SignedIncidence.targetMatrix,
        SignedIncidence.terminalDiagonal, incidenceMatrix, h]
    | inr j => simp [SignedIncidence.targetMatrix, incidenceMatrix]
  | inr i =>
    cases j with
    | inl j => simp [SignedIncidence.targetMatrix, incidenceMatrix]
    | inr j =>
      by_cases h : i = j <;> simp [SignedIncidence.targetMatrix,
        SignedIncidence.mediatorDiagonal, incidenceMatrix, h]

end GenericIncidence

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

/-- Degree three is supplied by the actual compiled and routed source. -/
theorem source_incidence_norm_le (β : SourceIncidence.E S precision → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hβ : ∀ e, |β e| ≤ R) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix (SourceIncidence.graph S precision) β)‖ ≤
      3 * R :=
  incidenceMatrix_norm_le _ β R hR hβ (SourceIncidence.degree_le_three S precision)

end Maxwell.Composition.PhysicalBright
