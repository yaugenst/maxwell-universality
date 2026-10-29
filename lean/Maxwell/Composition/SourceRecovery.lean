import Maxwell.Composition.SourceMediator
import Maxwell.Composition.ResidualFactor

/-! The actual midpoint Schur residual and finite selected-coordinate readout
imply the original rational sparse-source residual, uniformly in every state. -/
noncomputable section
namespace Maxwell.Composition.SourceRecovery
open Maxwell.Logical
open scoped Matrix.Norms.L2Operator

def residualFactor (S : Source.SparseSystem) (precision : ℕ) : ℕ :=
  routedResidualFactor S precision (1024 * SourceRouting.side S precision)

theorem residualFactor_bound (S : Source.SparseSystem) (precision : ℕ) :
    4 * Real.sqrt (S.n : ℝ) * ((((sourceCircuit S precision).size : ℝ) + 1)^2 + 1) *
      (1 + 2 * SourceSubdivision.ell S precision) ≤ (residualFactor S precision : ℝ) := by
  have h := mul_le_mul_of_nonneg_right (positiveResidualFactor_bound S precision)
    (show 0 ≤ 1 + 2 * SourceSubdivision.ell S precision by
      have := SourceSubdivision.ell_ge_one S precision; linarith)
  simpa only [residualFactor, routedResidualFactor, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat, SourceSubdivision.ell] using h

theorem source_output_residual (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (precision : ℕ) (hp : 1 ≤ precision) (L eta α ε : ℝ)
    (hL : 1 ≤ L) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hα : 0 < α)
    (hK : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hprecision : (S.nnz : ℝ) / (2 * 2 ^ precision) ≤ eta / (64 * L))
    (β : SourceIncidence.E S precision → ℝ) (hβ : ∀ e, 3 * α ≤ |β e|)
    (z : EuclideanSpace ℝ (SourceDecoration.Vertex S precision)) (zq : Fin S.n → ℚ)
    (hres : ‖SourceMediator.operator S precision α β z - SourceMediator.source S precision α‖ ≤
      α * ε * ‖SourceSubdivision.source S precision‖ / 64)
    (hbudget : (residualFactor S precision : ℝ) * ε ≤ eta)
    (hread : ∀ i, |(zq i : ℝ) - z (Sum.inl (SourceRouting.inputCoordinate S precision i))| ≤
      eta / (16 * S.nnz)) :
    Source.ResidualTarget S (eta / 4) (PositiveRecovery.decode S zq) := by
  apply SourceSubdivision.source_output_residual S hunit hm hb precision hp L eta
    hL heta heta1 hK hprecision (sumLeftProjection z) zq
  · calc
      _ ≤ (residualFactor S precision : ℝ) *
          ‖SourceSubdivision.operator S precision (sumLeftProjection z) - SourceSubdivision.source S precision‖ :=
        mul_le_mul_of_nonneg_right (residualFactor_bound S precision) (norm_nonneg _)
      _ ≤ (residualFactor S precision : ℝ) * ((4 / α) *
          ‖SourceMediator.operator S precision α β z - SourceMediator.source S precision α‖) :=
        mul_le_mul_of_nonneg_left (SourceMediator.routed_residual S precision α β hα hβ z) (by positivity)
      _ ≤ (residualFactor S precision : ℝ) * ((4 / α) *
          (α * ε * ‖SourceSubdivision.source S precision‖ / 64)) := by
        gcongr
      _ = ((residualFactor S precision : ℝ) * ε) * ‖SourceSubdivision.source S precision‖ / 16 := by
        field_simp
        ring
      _ ≤ (eta / 16) * ‖SourceSubdivision.source S precision‖ := by
        have h := mul_le_mul_of_nonneg_right hbudget (norm_nonneg (SourceSubdivision.source S precision))
        linarith
  · exact hread

end Maxwell.Composition.SourceRecovery
