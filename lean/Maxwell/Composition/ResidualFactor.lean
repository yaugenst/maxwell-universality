import Maxwell.Composition.PositiveRecovery
import Maxwell.Composition.ModePrecision

/-! Explicit integer residual amplification used by the parameter program.
The conservative bound follows from the constructed compiler; it avoids
real square roots in precision selection and retains polynomial dependence. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Logical

def positiveResidualFactor (S : Source.SparseSystem) (precision : ℕ) : ℕ :=
  4 * S.n * (((sourceCircuit S precision).size + 1)^2 + 1)

def routedResidualFactor (S : Source.SparseSystem) (precision ell : ℕ) : ℕ :=
  positiveResidualFactor S precision * (1 + 2 * ell)

theorem positiveResidualFactor_pos (S : Source.SparseSystem) (hn : 0 < S.n) (precision : ℕ) :
    0 < positiveResidualFactor S precision := by
  unfold positiveResidualFactor
  positivity

theorem routedResidualFactor_pos (S : Source.SparseSystem) (hn : 0 < S.n)
    (precision ell : ℕ) : 0 < routedResidualFactor S precision ell := by
  exact Nat.mul_pos (positiveResidualFactor_pos S hn precision) (by omega)

theorem positiveResidualFactor_bound (S : Source.SparseSystem) (precision : ℕ) :
    4 * Real.sqrt (S.n : ℝ) * ((((sourceCircuit S precision).size : ℝ) + 1)^2 + 1) ≤
      (positiveResidualFactor S precision : ℝ) := by
  have h := sqrt_nat_le S.n
  simp only [positiveResidualFactor, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow]
  gcongr

theorem positive_integer_residual_bound (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hp : 1 ≤ precision)
    (z : EuclideanSpace ℝ (SourcePositive.Vertex S precision)) :
    ‖Normalization.roundedOperator S precision (PositiveRecovery.input S precision z) -
        Source.rationalVector (Normalization.normalizedSource S)‖ ≤
      (positiveResidualFactor S precision : ℝ) *
        ‖PositiveEdges.operator (SourcePositive.sourceH S precision) z - PositiveRecovery.source S precision‖ :=
  (PositiveRecovery.rounded_graph_residual_le S hm precision hp z).trans
    (mul_le_mul_of_nonneg_right (positiveResidualFactor_bound S precision) (norm_nonneg _))

/-- Literal integer budget for the finite decoder's original-source theorem. -/
theorem positive_source_output_residual (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (precision : ℕ) (hp : 1 ≤ precision) (L eta : ℝ)
    (hL : 1 ≤ L) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hK : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hprecision : (S.nnz : ℝ) / (2 * 2 ^ precision) ≤ eta / (64 * L))
    (z : EuclideanSpace ℝ (SourcePositive.Vertex S precision)) (zq : Fin S.n → ℚ)
    (hres : (positiveResidualFactor S precision : ℝ) *
      ‖PositiveEdges.operator (SourcePositive.sourceH S precision) z - PositiveRecovery.source S precision‖ ≤
      (eta / 16) * ‖Source.rationalVector (Normalization.normalizedSource S)‖)
    (hread : ∀ i, |(zq i : ℝ) - z (SourcePositive.inputCoordinate S precision i)| ≤
      eta / (16 * S.nnz)) :
    Source.ResidualTarget S (eta / 4) (PositiveRecovery.decode S zq) :=
  PositiveRecovery.source_output_residual S hunit hm hb precision hp L eta hL heta heta1 hK hprecision z zq
    ((mul_le_mul_of_nonneg_right (positiveResidualFactor_bound S precision) (norm_nonneg _)).trans hres)
    hread

end Maxwell.Composition
