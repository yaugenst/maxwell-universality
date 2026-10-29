import Maxwell.Composition.SourceRouting
import Maxwell.Composition.SubdivisionSchur
import Maxwell.Composition.PositiveRecovery
import Maxwell.Composition.SourceAmplitude

/-! The actual routed matrix and source obtained from a sparse source system.
Its inverse is constructed from the compiled source, and every internal-path
residual is retained through the final rational source readout. -/

noncomputable section
namespace Maxwell.Composition.SourceSubdivision

open Maxwell.Logical
open Maxwell.Logical.Routing

local instance (S : Source.SparseSystem) (precision : ℕ) :
    DecidableEq (SourceRouting.Vertex S precision) := Classical.decEq _

/-- The matrix on exactly the vertices of the constructed lattice paths. -/
def matrix (S : Source.SparseSystem) (precision : ℕ) :
    Matrix (SourceRouting.Vertex S precision) (SourceRouting.Vertex S precision) ℝ :=
  SubdivisionSchur.matrix (SourceRouting.data S precision) (SourcePositive.graph S precision)
    (PositiveEdges.diagonal (SourcePositive.sourceH S precision))

def operator (S : Source.SparseSystem) (precision : ℕ) :
    EuclideanSpace ℝ (SourceRouting.Vertex S precision) →L[ℝ]
      EuclideanSpace ℝ (SourceRouting.Vertex S precision) :=
  SubdivisionSchur.operator (SourceRouting.data S precision) (SourcePositive.graph S precision)
    (PositiveEdges.diagonal (SourcePositive.sourceH S precision))

@[simp] theorem operator_eq_matrix (S : Source.SparseSystem) (precision : ℕ) :
    operator S precision = Matrix.toEuclideanCLM
      (n := SourceRouting.Vertex S precision) (𝕜 := ℝ) (matrix S precision) := rfl

/-- The source is supported on the original positive-graph vertices. -/
def source (S : Source.SparseSystem) (precision : ℕ) :
    EuclideanSpace ℝ (SourceRouting.Vertex S precision) :=
  sumLeftInjection (κ := SubdivisionSchur.Internal (SourceRouting.data S precision))
    (PositiveRecovery.source S precision)

def input (S : Source.SparseSystem) (precision : ℕ)
    (z : EuclideanSpace ℝ (SourceRouting.Vertex S precision)) : EuclideanSpace ℝ (Fin S.n) :=
  PositiveRecovery.input S precision (sumLeftProjection z)

@[simp] theorem input_coordinate (S : Source.SparseSystem) (precision : ℕ)
    (z : EuclideanSpace ℝ (SourceRouting.Vertex S precision)) (i : Fin S.n) :
    input S precision z i = z (SourceRouting.inputCoordinate S precision i) := rfl

/-- A uniform upper bound for every actual internal path length. -/
def ell (S : Source.SparseSystem) (precision : ℕ) : ℝ :=
  1024 * SourceRouting.side S precision

theorem ell_ge_one (S : Source.SparseSystem) (precision : ℕ) : 1 ≤ ell S precision := by
  have hs : (1 : ℝ) ≤ SourceRouting.side S precision := by
    exact_mod_cast SourceRouting.side_pos S precision
  dsimp only [ell]
  linarith

theorem internal_length_le (S : Source.SparseSystem) (precision : ℕ)
    (e : SourceRouting.Edge S precision) :
    (((EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length - 1 : ℕ) : ℝ) ≤
      ell S precision := by
  have h := SourceRouting.edge_length_le S precision e
  have hh : (EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length - 1 ≤
      1024 * SourceRouting.side S precision := by omega
  unfold ell
  exact_mod_cast hh

theorem source_norm (S : Source.SparseSystem) (precision : ℕ) :
    ‖source S precision‖ = ‖Source.rationalVector (Normalization.normalizedSource S)‖ := by
  exact (sumLeftInjection_norm_apply
    (κ := SubdivisionSchur.Internal (SourceRouting.data S precision))
    (PositiveRecovery.source S precision)).trans (PositiveRecovery.source_norm S precision)

theorem source_norm_bounds (S : Source.SparseSystem) (hb : S.source ≠ 0) (precision : ℕ) :
    1 ≤ ‖source S precision‖ ∧ ‖source S precision‖ ≤ Real.sqrt (S.n : ℝ) := by
  rw [source_norm]
  exact ⟨Normalization.normalizedSource_norm_ge_one S hb,
    Normalization.normalizedSource_norm_le S hb⟩

/-- The terminal Schur matrix is the actual compiled positive matrix. -/
theorem positive_operator_eq (S : Source.SparseSystem) (precision : ℕ) :
    Matrix.toEuclideanCLM (n := SourcePositive.Vertex S precision) (𝕜 := ℝ)
      ((SourcePositive.graph S precision).logicalMatrix
        (PositiveEdges.diagonal (SourcePositive.sourceH S precision))) =
      PositiveEdges.operator (SourcePositive.sourceH S precision) := by
  change Matrix.toEuclideanCLM (n := SourcePositive.Vertex S precision) (𝕜 := ℝ)
    ((PositiveEdges.positiveGraph (SourcePositive.sourceH S precision)).logicalMatrix
      (PositiveEdges.diagonal (SourcePositive.sourceH S precision))) = _
  rw [← PositiveEdges.matrix_eq_graph]
  rfl

theorem terminal_equiv_coe (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    (SourcePositive.equiv S hunit hm precision hp hsmall :
      EuclideanSpace ℝ (SourcePositive.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourcePositive.Vertex S precision)) =
      Matrix.toEuclideanCLM (n := SourcePositive.Vertex S precision) (𝕜 := ℝ)
        ((SourcePositive.graph S precision).logicalMatrix
          (PositiveEdges.diagonal (SourcePositive.sourceH S precision))) := by
  rw [positive_operator_eq]
  rfl

/-- The accuracy precision budget also supplies the inverse-perturbation
budget used by the actual rounded source equivalence. -/
theorem rounding_small (S : Source.SparseSystem) (precision : ℕ) (L eta : ℝ)
    (hL : 1 ≤ L) (heta1 : eta ≤ 1)
    (hK : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hprecision : (S.nnz : ℝ) / (2 * 2 ^ precision) ≤ eta / (64 * L)) :
    ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2 := by
  have hL0 : 0 < L := by linarith
  calc
    _ ≤ L * (eta / (64 * L)) :=
      mul_le_mul hK hprecision (by positivity) hL0.le
    _ = eta / 64 := by field_simp [ne_of_gt hL0]
    _ ≤ 1 / 2 := by linarith

/-- Full routed invertibility follows from the actual rounded source inverse
and the explicit chronological path inverses. -/
def equiv (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    EuclideanSpace ℝ (SourceRouting.Vertex S precision) ≃L[ℝ]
      EuclideanSpace ℝ (SourceRouting.Vertex S precision) :=
  SubdivisionSchur.equiv (SourceRouting.data S precision) (SourcePositive.graph S precision)
    (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
    (SourcePositive.equiv S hunit hm precision hp hsmall)
    (terminal_equiv_coe S hunit hm precision hp hsmall)

@[simp] theorem equiv_coe (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    (equiv S hunit hm precision hp hsmall :
      EuclideanSpace ℝ (SourceRouting.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourceRouting.Vertex S precision)) = operator S precision := rfl

theorem inverse_norm_le (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2)
    (L : ℝ) (hL : 1 ≤ L)
    (hcondition : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L) :
    ‖((equiv S hunit hm precision hp hsmall).symm :
      EuclideanSpace ℝ (SourceRouting.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourceRouting.Vertex S precision))‖ ≤
      9 * ell S precision ^ 2 *
        (256 * L * ((sourceCircuit S precision).size : ℝ) ^ 4 + ell S precision) :=
  SubdivisionSchur.inverse_norm_le_polynomial (SourceRouting.data S precision)
    (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
    (SourcePositive.degree_le_three S precision)
    (SourcePositive.equiv S hunit hm precision hp hsmall)
    (terminal_equiv_coe S hunit hm precision hp hsmall)
    (ell S precision) _ (ell_ge_one S precision) (internal_length_le S precision)
    (SourcePositive.inverse_norm_le S hunit hm precision hp hsmall L hL hcondition)

/-- No equation on the internal path vertices is required to be exact. -/
theorem positive_residual_le (S : Source.SparseSystem) (precision : ℕ)
    (z : EuclideanSpace ℝ (SourceRouting.Vertex S precision)) :
    ‖PositiveEdges.operator (SourcePositive.sourceH S precision) (sumLeftProjection z) -
      PositiveRecovery.source S precision‖ ≤ (1 + 2 * ell S precision) *
        ‖operator S precision z - source S precision‖ := by
  have h := SubdivisionSchur.residual_transfer (SourceRouting.data S precision)
    (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
    (SourcePositive.degree_le_three S precision) (ell S precision)
    (by have := ell_ge_one S precision; linarith) (internal_length_le S precision)
    z (PositiveRecovery.source S precision)
  rw [positive_operator_eq] at h
  exact h

theorem rounded_residual_le (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hp : 1 ≤ precision)
    (z : EuclideanSpace ℝ (SourceRouting.Vertex S precision)) :
    ‖Normalization.roundedOperator S precision (input S precision z) -
      Source.rationalVector (Normalization.normalizedSource S)‖ ≤
      4 * Real.sqrt (S.n : ℝ) *
        ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        (1 + 2 * ell S precision) * ‖operator S precision z - source S precision‖ := by
  calc
    _ ≤ 4 * Real.sqrt (S.n : ℝ) *
        ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        ‖PositiveEdges.operator (SourcePositive.sourceH S precision) (sumLeftProjection z) -
          PositiveRecovery.source S precision‖ :=
      PositiveRecovery.rounded_graph_residual_le S hm precision hp (sumLeftProjection z)
    _ ≤ 4 * Real.sqrt (S.n : ℝ) *
        ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        ((1 + 2 * ell S precision) * ‖operator S precision z - source S precision‖) :=
      mul_le_mul_of_nonneg_left (positive_residual_le S precision z) (by positivity)
    _ = _ := by ring

/-- Finite coordinate rounding of any routed approximate state yields the
required original sparse-source residual under the explicit error budgets. -/
theorem source_output_residual (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (precision : ℕ) (hp : 1 ≤ precision) (L eta : ℝ)
    (hL : 1 ≤ L) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hK : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hprecision : (S.nnz : ℝ) / (2 * 2 ^ precision) ≤ eta / (64 * L))
    (z : EuclideanSpace ℝ (SourceRouting.Vertex S precision)) (zq : Fin S.n → ℚ)
    (hres : 4 * Real.sqrt (S.n : ℝ) *
      ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
      (1 + 2 * ell S precision) * ‖operator S precision z - source S precision‖ ≤
      (eta / 16) * ‖source S precision‖)
    (hread : ∀ i, |(zq i : ℝ) - z (SourceRouting.inputCoordinate S precision i)| ≤
      eta / (16 * S.nnz)) :
    Source.ResidualTarget S (eta / 4) (PositiveRecovery.decode S zq) := by
  apply PositiveRecovery.source_output_residual S hunit hm hb precision hp L eta
    hL heta heta1 hK hprecision (sumLeftProjection z) zq
  · calc
      _ ≤ 4 * Real.sqrt (S.n : ℝ) *
          ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
          ((1 + 2 * ell S precision) * ‖operator S precision z - source S precision‖) :=
        mul_le_mul_of_nonneg_left (positive_residual_le S precision z) (by positivity)
      _ = 4 * Real.sqrt (S.n : ℝ) *
          ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
          (1 + 2 * ell S precision) * ‖operator S precision z - source S precision‖ := by ring
      _ ≤ (eta / 16) * ‖source S precision‖ := hres
      _ = _ := by rw [source_norm]
  · exact hread

end Maxwell.Composition.SourceSubdivision
