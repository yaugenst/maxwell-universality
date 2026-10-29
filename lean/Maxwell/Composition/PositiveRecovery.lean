import Maxwell.Composition.SourcePositive
import Maxwell.Composition.SourceResidual
import Maxwell.Logical.InputRecovery

/-! Actual source and finite rational readout for the compiled positive graph.
All graph equations may have residuals. The only accuracy premise is their
explicit norm budget, followed by coordinate quantization of the readout. -/

noncomputable section

namespace Maxwell.Composition.PositiveRecovery

open Maxwell.Logical

def source (S : Source.SparseSystem) (precision : ℕ) :
    EuclideanSpace ℝ (SourcePositive.Vertex S precision) :=
  PositiveEdges.source (SourcePositive.sourceH S precision)
    (SourceResidual.sourceBoundary S precision
      (Source.rationalVector (Normalization.normalizedSource S)))

def input (S : Source.SparseSystem) (precision : ℕ)
    (z : EuclideanSpace ℝ (SourcePositive.Vertex S precision)) :
    EuclideanSpace ℝ (Fin S.n) :=
  WithLp.toLp 2 ((sourceCircuit S precision).circuit.originalInput
    (WithLp.ofLp (PositiveEdges.readout (SourcePositive.sourceH S precision) z)))

def decode (S : Source.SparseSystem) (zq : Fin S.n → ℚ) : Fin S.n → ℚ :=
  fun i => (Normalization.sourceScale S / Normalization.matrixScale S) * zq i

@[simp] theorem input_coordinate (S : Source.SparseSystem) (precision : ℕ)
    (z : EuclideanSpace ℝ (SourcePositive.Vertex S precision)) (i : Fin S.n) :
    input S precision z i = z (SourcePositive.inputCoordinate S precision i) := rfl

theorem source_norm (S : Source.SparseSystem) (precision : ℕ) :
    ‖source S precision‖ = ‖Source.rationalVector (Normalization.normalizedSource S)‖ := by
  rw [source, PositiveEdges.source_norm, SourceResidual.sourceBoundary_norm]

theorem rounded_graph_residual_le (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hp : 1 ≤ precision)
    (z : EuclideanSpace ℝ (SourcePositive.Vertex S precision)) :
    ‖Normalization.roundedOperator S precision (input S precision z) -
        Source.rationalVector (Normalization.normalizedSource S)‖ ≤
      4 * Real.sqrt (S.n : ℝ) *
        ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        ‖PositiveEdges.operator (SourcePositive.sourceH S precision) z - source S precision‖ := by
  let y := PositiveEdges.readout (SourcePositive.sourceH S precision) z
  let g := Source.rationalVector (Normalization.normalizedSource S)
  have hgraph := PositiveEdges.full_residual_transfer (SourcePositive.sourceH S precision)
    (SourcePositive.alphabet S precision) (SourcePositive.rowSupport_le_three S precision)
    (SourcePositive.columnSupport_le_three S precision) z
    (SourceResidual.sourceBoundary S precision g)
  rw [← SourcePositive.sourceH_operator] at hgraph
  have hcircuit := SourceResidual.rounded_residual_norm_le S hm precision hp y g
  have heq : Normalization.roundedOperator S precision (input S precision z) =
      WithLp.toLp 2 (roundedProduct S precision
        ((sourceCircuit S precision).circuit.originalInput (WithLp.ofLp y))) := rfl
  rw [heq]
  calc
    _ ≤ Real.sqrt (S.n : ℝ) *
        ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        ‖sourceSquareOperator S precision y - SourceResidual.sourceBoundary S precision g‖ :=
      hcircuit
    _ ≤ Real.sqrt (S.n : ℝ) *
        ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
        (4 * ‖PositiveEdges.operator (SourcePositive.sourceH S precision) z -
          source S precision‖) :=
      mul_le_mul_of_nonneg_left hgraph (by positivity)
    _ = _ := by ring

/-- Finite rational coordinate samples of an arbitrary approximate positive
graph state solve the original sparse source to relative residual `eta/4`. -/
theorem source_output_residual (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (precision : ℕ) (hp : 1 ≤ precision) (L eta : ℝ)
    (hL : 1 ≤ L) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hK : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hprecision : (S.nnz : ℝ) / (2 * 2 ^ precision) ≤ eta / (64 * L))
    (z : EuclideanSpace ℝ (SourcePositive.Vertex S precision)) (zq : Fin S.n → ℚ)
    (hres : 4 * Real.sqrt (S.n : ℝ) *
      ((((sourceCircuit S precision).size : ℝ) + 1) ^ 2 + 1) *
      ‖PositiveEdges.operator (SourcePositive.sourceH S precision) z - source S precision‖ ≤
      (eta / 16) * ‖Source.rationalVector (Normalization.normalizedSource S)‖)
    (hread : ∀ i, |(zq i : ℝ) - z (SourcePositive.inputCoordinate S precision i)| ≤
      eta / (16 * S.nnz)) :
    Source.ResidualTarget S (eta / 4) (decode S zq) := by
  exact Normalization.source_output_residual S hunit (by omega) hb precision L eta
    (by linarith) heta heta1 hK hprecision (input S precision z) zq
    ((rounded_graph_residual_le S hm precision hp z).trans hres)
    (by simpa only [input_coordinate] using hread)

end Maxwell.Composition.PositiveRecovery
