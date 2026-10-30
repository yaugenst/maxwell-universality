import Maxwell.Continuum.FiniteAuxiliaryRoutedSource
import Maxwell.Composition.SubdivisionNorm

/-! The literal real routed readout of complex physical moments. It is
a contraction, and the actual routed matrix has norm at most six. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition ComplexInverse

theorem complexTerminalPart_norm_le {V E : Type*} [Fintype V] [Fintype E]
    (z : EuclideanSpace ℂ (V ⊕ E)) : ‖complexTerminalPart z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  change (∑ i : V, ‖z (Sum.inl i)‖^2) ≤
    (∑ i : V, ‖z (Sum.inl i)‖^2)+(∑ i : E, ‖z (Sum.inr i)‖^2)
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

def routedReadout (S : Source.SparseSystem) (precision : ℕ)
    (z : EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) :
    EuclideanSpace ℝ (SourceIncidence.V S precision) :=
  realPart (complexTerminalPart z)

theorem routedReadout_norm_le (S : Source.SparseSystem) (precision : ℕ)
    (z : EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) :
    ‖routedReadout S precision z‖ ≤ ‖z‖ :=
  (realPart_norm_le _).trans (complexTerminalPart_norm_le z)

theorem routedReadout_sub (S : Source.SparseSystem) (precision : ℕ)
    (z w : EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) :
    routedReadout S precision (z-w) = routedReadout S precision z-routedReadout S precision w := by
  ext i
  rfl

theorem routedReadout_stability (S : Source.SparseSystem) (precision : ℕ)
    (z w : EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) :
    ‖routedReadout S precision z-routedReadout S precision w‖ ≤ ‖z-w‖ := by
  rw [← routedReadout_sub]
  exact routedReadout_norm_le S precision _

variable (S : Source.SparseSystem) (precision : ℕ)
local instance routedReadoutDecidableEq : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem routed_real_residual (z : EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) :
    ‖SourceSubdivision.operator S precision (routedReadout S precision z)-SourceSubdivision.source S precision‖ ≤
      ‖complexOperator ((SourceIncidence.graph S precision).logicalMatrix (SourceMediator.diagonal S precision))
        (complexTerminalPart z)-ofRealVector (SourceSubdivision.source S precision)‖ := by
  have he : realPart
      (complexOperator ((SourceIncidence.graph S precision).logicalMatrix (SourceMediator.diagonal S precision))
        (complexTerminalPart z)-ofRealVector (SourceSubdivision.source S precision)) =
      SourceSubdivision.operator S precision (routedReadout S precision z)-SourceSubdivision.source S precision := by
    rw [realPart_sub, complexOperator_realPart]
    change Matrix.toEuclideanCLM (n := SourceIncidence.V S precision) (𝕜 := ℝ)
      ((SourceIncidence.graph S precision).logicalMatrix (SourceMediator.diagonal S precision))
      (routedReadout S precision z)-realPart (ofRealVector (SourceSubdivision.source S precision)) = _
    rw [SourceMediator.logical_operator_eq]
    rfl
  rw [← he]
  exact realPart_norm_le _

theorem routed_residual_stability (z w : EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) :
    ‖SourceSubdivision.operator S precision (routedReadout S precision z)-SourceSubdivision.source S precision‖ ≤
      6*‖z-w‖+
        ‖SourceSubdivision.operator S precision (routedReadout S precision w)-SourceSubdivision.source S precision‖ := by
  have he : SourceSubdivision.operator S precision (routedReadout S precision z)-SourceSubdivision.source S precision =
      SourceSubdivision.operator S precision (routedReadout S precision z-routedReadout S precision w)+
      (SourceSubdivision.operator S precision (routedReadout S precision w)-SourceSubdivision.source S precision) := by
    rw [map_sub]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  exact ((SourceSubdivision.operator S precision).le_of_opNorm_le
    (SourceSubdivision.operator_norm_le_six S precision) _).trans
    (mul_le_mul_of_nonneg_left (routedReadout_stability S precision z w) (by norm_num))

#print axioms routed_real_residual
#print axioms routed_residual_stability

end Maxwell.Continuum.FiniteAuxiliary
