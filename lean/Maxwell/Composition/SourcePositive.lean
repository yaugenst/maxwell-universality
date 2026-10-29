import Maxwell.Composition.PositiveTransform
import Maxwell.Composition.PositiveNorm
import Maxwell.Composition.CircuitColumns
import Maxwell.Logical.SourceInverse
import Maxwell.Logical.CompilerFanout
import Maxwell.Logical.CircuitRows

/-! Binding the actual sparse-source compiler to its concrete positive graph.
Row and column degree, the finite coefficient alphabet and the full inverse
are derived from the constructed compiler. -/
noncomputable section
namespace Maxwell.Composition.SourcePositive
open Maxwell.Logical
open Matrix

def sourceH (S : Source.SparseSystem) (precision : ℕ) :
    Matrix (Fin (sourceCircuit S precision).size) (Fin (sourceCircuit S precision).size) ℝ :=
  (sourceSquareMap S precision).toMatrix'

theorem sourceOutput_list (S : Source.SparseSystem) (precision : ℕ) :
    List.ofFn (sourceOutput S precision) = (sourceCircuit S precision).outputs := by
  apply List.ext_getElem
  · simp [sourceCircuit_output_count]
  · intro i hi hj
    simp [sourceOutput]

theorem columnSupport_le_three (S : Source.SparseSystem) (precision : ℕ)
    (j : Fin (sourceCircuit S precision).size) :
    (PositiveEdges.columnSupport (sourceH S precision) j).card ≤ 3 := by
  apply CircuitColumns.squareMap_columnSupport_le_three
    (sourceCircuit S precision).circuit (sourceOutput S precision)
  intro k
  rw [sourceOutput_list]
  exact sourceCircuit_charged S precision k

theorem rowSupport_le_three (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceCircuit S precision).size) :
    (PositiveEdges.rowSupport (sourceH S precision) i).card ≤ 3 :=
  (sourceCircuit_smallGates S precision).squareMap_rowSupport_le_three (sourceOutput S precision) i

theorem alphabet (S : Source.SparseSystem) (precision : ℕ) :
    PositiveEdges.Alphabet (sourceH S precision) := by
  intro i j
  exact (sourceCircuit_smallGates S precision).squareMap_alphabet (sourceOutput S precision) i j

theorem sourceH_operator (S : Source.SparseSystem) (precision : ℕ) :
    sourceSquareOperator S precision =
      Matrix.toEuclideanCLM (n := Fin (sourceCircuit S precision).size) (𝕜 := ℝ)
        (sourceH S precision) := by
  ext x i
  change sourceSquareMap S precision (WithLp.ofLp x) i =
    ((sourceSquareMap S precision).toMatrix' *ᵥ WithLp.ofLp x) i
  exact congrFun (LinearMap.toMatrix'_mulVec (sourceSquareMap S precision) (WithLp.ofLp x)).symm i

theorem sourceH_equiv (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    (sourceSquareEuclideanEquiv S hunit hm precision hs hsmall :
      EuclideanSpace ℝ (Fin (sourceCircuit S precision).size) →L[ℝ]
        EuclideanSpace ℝ (Fin (sourceCircuit S precision).size)) =
      Matrix.toEuclideanCLM (n := Fin (sourceCircuit S precision).size) (𝕜 := ℝ)
        (sourceH S precision) := by
  rw [← sourceH_operator]
  ext x i
  rfl

abbrev Vertex (S : Source.SparseSystem) (precision : ℕ) :=
  ((Fin (sourceCircuit S precision).size ⊕ Fin (sourceCircuit S precision).size) ⊕
    PositiveEdges.Edge (sourceH S precision))

def matrix (S : Source.SparseSystem) (precision : ℕ) :
    Matrix (Vertex S precision) (Vertex S precision) ℝ :=
  PositiveEdges.matrix (sourceH S precision)

def graph (S : Source.SparseSystem) (precision : ℕ) :=
  PositiveEdges.positiveGraph (sourceH S precision)

def inputCoordinate (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    Vertex S precision :=
  Sum.inl (Sum.inr ((sourceCircuit S precision).circuit.inputIndex i))

theorem inputCoordinate_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (inputCoordinate S precision) := by
  intro i j hij
  apply (sourceCircuit S precision).circuit.inputIndex_injective
  exact Sum.inr.inj (Sum.inl.inj hij)

/-- This full inverse is built from the actual original source's rounded
circuit equivalence; full positive-graph invertibility is never a premise. -/
def equiv (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    EuclideanSpace ℝ (Vertex S precision) ≃L[ℝ] EuclideanSpace ℝ (Vertex S precision) :=
  PositiveEdges.fullEquiv (sourceH S precision)
    (sourceSquareEuclideanEquiv S hunit hm precision hs hsmall)
    (sourceH_equiv S hunit hm precision hs hsmall)

@[simp] theorem equiv_coe (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    (equiv S hunit hm precision hs hsmall : EuclideanSpace ℝ (Vertex S precision) →L[ℝ]
      EuclideanSpace ℝ (Vertex S precision)) =
      Matrix.toEuclideanCLM (n := Vertex S precision) (𝕜 := ℝ) (matrix S precision) := rfl

theorem inverse_norm_le (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (precision : ℕ)
    (hs : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2)
    (L : ℝ) (hL : 1 ≤ L)
    (hcondition : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L) :
    ‖((equiv S hunit hm precision hs hsmall).symm : EuclideanSpace ℝ (Vertex S precision) →L[ℝ]
      EuclideanSpace ℝ (Vertex S precision))‖ ≤
        256 * L * ((sourceCircuit S precision).size : ℝ) ^ 4 := by
  have hd : (2 : ℝ) ≤ (sourceCircuit S precision).size := by
    exact_mod_cast sourceCircuit_size_two_le S hm precision
  have hQ : 1 ≤ 16 * L * ((sourceCircuit S precision).size : ℝ)^4 := by
    have hp : 1 ≤ ((sourceCircuit S precision).size : ℝ)^4 := one_le_pow₀ (by linarith)
    nlinarith
  have h := PositiveEdges.full_inverse_norm_le (sourceH S precision)
    (sourceSquareEuclideanEquiv S hunit hm precision hs hsmall)
    (sourceH_equiv S hunit hm precision hs hsmall) (alphabet S precision) (rowSupport_le_three S precision)
    (columnSupport_le_three S precision) _ hQ
    (sourceSquare_inverse_norm_le S hunit hm precision hs hsmall L hL hcondition)
  convert h using 1
  · rfl
  · ring

theorem degree_le_three (S : Source.SparseSystem) (precision : ℕ)
    (v : Vertex S precision) : (graph S precision).degree v ≤ 3 :=
  PositiveEdges.positive_degree_le_three (sourceH S precision) (rowSupport_le_three S precision)
    (columnSupport_le_three S precision) v

theorem norm_le_six (S : Source.SparseSystem) (precision : ℕ) :
    ‖Matrix.toEuclideanCLM (n := Vertex S precision) (𝕜 := ℝ) (matrix S precision)‖ ≤ 6 :=
  PositiveEdges.matrix_norm_le_six (sourceH S precision) (alphabet S precision)
    (rowSupport_le_three S precision) (columnSupport_le_three S precision)

theorem vertex_count_le (S : Source.SparseSystem) (precision : ℕ) :
    Fintype.card (Vertex S precision) ≤ 5 * (sourceCircuit S precision).size := by
  simpa using PositiveEdges.vertex_card_le (sourceH S precision) (rowSupport_le_three S precision)

end Maxwell.Composition.SourcePositive
