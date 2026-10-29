import Maxwell.Composition.PhysicalFloor
import Maxwell.Composition.SourceVertexList

/-! Exact rational diagonal tuning data for the physical midpoint graph.
The scalar margin follows from the fixed floor and the calibrated coupling
size; every diagonal is a literal rational expression. -/
noncomputable section
namespace Maxwell.Composition.PhysicalDiagonal
open Maxwell.Spectral Maxwell.Spectral.Lattice
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

def degree (v : SourceIncidence.V S precision) : ℕ :=
  (Finset.univ.filter (fun e : SourceIncidence.E S precision => v = e.val.1 ∨ v = e.val.2)).card

theorem degree_cast (v : SourceIncidence.V S precision) :
    (degree S precision v : ℝ) = (SourceIncidence.graph S precision).degree v := by
  simp only [degree, Finset.natCast_card_filter, SignedIncidence.degree, SourceIncidence.graph]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : v = e.val.1 ∨ v = e.val.2 <;> simp [h]

theorem degree_le_three (v : SourceIncidence.V S precision) : degree S precision v ≤ 3 := by
  have h := SourceIncidence.degree_le_three S precision v
  rw [← degree_cast] at h
  exact_mod_cast h

def diagonal (α : ℚ) (β : Direction → ℚ) : SourceDecoration.Vertex S precision → ℚ
  | .inl v => α * (SourceVertexList.diagonal S precision v - degree S precision v)
  | .inr e => -(β (SourceIncidence.axis S precision e))^2 / α

theorem diagonal_cast (α : ℚ) (β : Direction → ℚ) (i : SourceDecoration.Vertex S precision) :
    (diagonal S precision α β i : ℝ) =
      (SourceIncidence.graph S precision).targetMatrix (α : ℝ)
        (fun e => (β (SourceIncidence.axis S precision e) : ℝ)) (SourceMediator.diagonal S precision) i i := by
  cases i with
  | inl v =>
    simp only [diagonal, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, degree_cast,
      SourceVertexList.diagonal_cast, SignedIncidence.targetMatrix, Matrix.fromBlocks_apply₁₁,
      SignedIncidence.terminalDiagonal, Matrix.diagonal_apply_eq, SourceMediator.diagonal]
  | inr e =>
    simp only [diagonal, Rat.cast_div, Rat.cast_neg, Rat.cast_pow, SignedIncidence.targetMatrix,
      Matrix.fromBlocks_apply₂₂, SignedIncidence.mediatorDiagonal, Matrix.diagonal_apply_eq]

theorem terminal_bound (α : ℚ) (hα : 0 ≤ α) (β : Direction → ℚ)
    (v : SourceIncidence.V S precision) : |(diagonal S precision α β (.inl v) : ℝ)| ≤ 6*(α : ℝ) := by
  have hαR : (0 : ℝ) ≤ α := by exact_mod_cast hα
  have hd := SourceSubdivision.diagonal_abs_le_three S precision v
  have hn : (degree S precision v : ℝ) ≤ 3 := by exact_mod_cast degree_le_three S precision v
  have hn0 : (0 : ℝ) ≤ degree S precision v := by positivity
  simp only [diagonal, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, SourceVertexList.diagonal_cast,
    abs_mul, abs_of_nonneg hαR]
  have hs := abs_sub_le (SourceSubdivision.matrix S precision v v) 0 (degree S precision v : ℝ)
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hn0] at hs
  have hbound : |SourceSubdivision.matrix S precision v v - (degree S precision v : ℝ)| ≤ 6 := by linarith
  nlinarith

theorem diagonal_bound (P : PhysicalPlatform) (d : ℕ) (hd : P.coreFloor ≤ d)
    (β : Direction → ℚ)
    (hβ : ∀ k, |(β k : ℝ)| ≤ ((P.greenConstant+1)*P.spacing.zeta d : ℚ))
    (i : SourceDecoration.Vertex S precision) :
    |(diagonal S precision (P.spacing.alpha d) β i : ℝ)| ≤ (P.tuningMargin : ℝ) := by
  have hα : (0 : ℝ) < P.spacing.alpha d := by exact_mod_cast P.spacing.alpha_pos d
  cases i with
  | inl v =>
    exact (terminal_bound S precision _ (P.spacing.alpha_pos d).le β v).trans
      (by exact_mod_cast P.coreFloor_alpha d hd)
  | inr e =>
    have hb := hβ (SourceIncidence.axis S precision e)
    have hb0 : (0 : ℝ) ≤ ((P.greenConstant+1)*P.spacing.zeta d : ℚ) := by
      exact_mod_cast mul_nonneg (by linarith [P.greenConstant_nonneg]) (P.spacing.zeta_pos d).le
    have hsq := pow_le_pow_left₀ (abs_nonneg (β (SourceIncidence.axis S precision e) : ℝ)) hb 2
    rw [sq_abs] at hsq
    have hratio := div_le_div_of_nonneg_right hsq hα.le
    have hfloor := P.coreFloor_mediator d hd
    have hfloorR : (((P.greenConstant+1)*P.spacing.zeta d : ℚ) : ℝ)^2 /
        (P.spacing.alpha d : ℝ) ≤ (P.tuningMargin : ℝ) := by exact_mod_cast hfloor
    simp only [diagonal, Rat.cast_div, Rat.cast_neg, Rat.cast_pow, abs_div, abs_neg,
      abs_of_pos hα, abs_sq]
    exact hratio.trans hfloorR

/-- Actual calibrated inverse strengths meet the Neumann smallness budget
for the complete finite complement, with the fixed floor supplying every
scalar inequality. -/
theorem inverse_strength_budget (P : PhysicalPlatform) (d : ℕ) (hd : P.coreFloor ≤ d)
    (β : Direction → ℚ) (hβ : ∀ k, |(β k : ℝ)| ≤ ((P.greenConstant+1)*P.spacing.zeta d : ℚ))
    (v : SourceDecoration.Vertex S precision → ℚ)
    (hv : ∀ i, |(v i : ℝ)⁻¹ - (P.eigenvalue + (diagonal S precision (P.spacing.alpha d) β i : ℝ))| ≤
      (P.spacing.zeta d : ℝ)^2) :
    (∀ i, |(v i : ℝ)⁻¹ - P.eigenvalue| ≤ (P.tuningMargin : ℝ) + (P.spacing.zeta d : ℝ)^2) ∧
      ((P.tuningMargin : ℝ) + (P.spacing.zeta d : ℝ)^2) +
        64*(P.greenConstant : ℝ)*(P.spacing.zeta d : ℝ) + (P.spacing.zeta d : ℝ)^2 ≤ (P.defectGap : ℝ)/2 := by
  constructor
  · intro i
    have ht := diagonal_bound S precision P d hd β hβ i
    have he := abs_add_le ((v i : ℝ)⁻¹ - (P.eigenvalue +
      (diagonal S precision (P.spacing.alpha d) β i : ℝ)))
      (diagonal S precision (P.spacing.alpha d) β i : ℝ)
    have hx : (v i : ℝ)⁻¹ - (P.eigenvalue + (diagonal S precision (P.spacing.alpha d) β i : ℝ)) +
        (diagonal S precision (P.spacing.alpha d) β i : ℝ) = (v i : ℝ)⁻¹ - P.eigenvalue := by ring
    rw [hx] at he
    linarith [hv i]
  · have hf : (P.tuningMargin : ℝ) + 64*(P.greenConstant : ℝ)*(P.spacing.zeta d : ℝ) +
        2*(P.spacing.zeta d : ℝ)^2 ≤ (P.defectGap : ℝ)/2 := by
      exact_mod_cast (P.coreFloor_small d hd).2.2
    linarith

end Maxwell.Composition.PhysicalDiagonal
