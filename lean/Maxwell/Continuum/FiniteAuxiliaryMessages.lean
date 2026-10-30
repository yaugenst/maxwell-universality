import Maxwell.Continuum.FiniteAuxiliaryRoutedReadout
import Maxwell.Composition.PhysicalAccuracy

/-! Literal rational messages for volume moments. Every coordinatewise
accurate message has a controlled routed residual, and the established
logical decoder then returns an answer to the original sparse system. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition ComplexInverse

theorem euclidean_norm_le_sum_norm {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    ‖z‖ ≤ ∑ i, ‖z i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

def rationalMomentVector {ι : Type*} (w : ι → ℚ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => ((w i : ℝ) : ℂ))

theorem rationalMomentVector_error {ι : Type*} [Fintype ι] (w : ι → ℚ)
    (z : EuclideanSpace ℂ ι) {δ : ℝ}
    (hw : ∀ i, |(w i : ℝ)-(z i).re| ≤ δ) :
    ‖rationalMomentVector w-ofRealVector (realPart z)‖ ≤ (Fintype.card ι : ℝ)*δ := by
  apply (euclidean_norm_le_sum_norm _).trans
  calc
    _ ≤ ∑ _i : ι, δ := by
      apply Finset.sum_le_sum
      intro i _
      change ‖((w i : ℝ) : ℂ)-((z i).re : ℂ)‖ ≤ δ
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hw i
    _ = _ := by simp

theorem routedReadout_realPart (S : Source.SparseSystem) (precision : ℕ)
    (z : EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) :
    routedReadout S precision (ofRealVector (realPart z)) = routedReadout S precision z := by
  ext i
  rfl

theorem message_routed_residual (S : Source.SparseSystem) (precision : ℕ)
    (w : SourceDecoration.Vertex S precision → ℚ)
    (z : EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) {δ : ℝ}
    (hw : ∀ i, |(w i : ℝ)-(z i).re| ≤ δ) :
    ‖SourceSubdivision.operator S precision (routedReadout S precision (rationalMomentVector w))-
      SourceSubdivision.source S precision‖ ≤
      6*(Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*δ+
        ‖SourceSubdivision.operator S precision (routedReadout S precision z)-
          SourceSubdivision.source S precision‖ := by
  have he := routed_residual_stability S precision (rationalMomentVector w) (ofRealVector (realPart z))
  rw [routedReadout_realPart] at he
  apply he.trans
  have hm := mul_le_mul_of_nonneg_left (rationalMomentVector_error w z hw) (by norm_num : (0 : ℝ) ≤ 6)
  simpa only [mul_assoc] using add_le_add hm
    (le_refl ‖SourceSubdivision.operator S precision (routedReadout S precision z)-
      SourceSubdivision.source S precision‖)

def sparseMomentDecode (S : Source.SparseSystem) (precision : ℕ)
    (w : SourceDecoration.Vertex S precision → ℚ) : Fin S.n → ℚ :=
  PositiveRecovery.decode S (fun i => w (Sum.inl (SourceRouting.inputCoordinate S precision i)))

theorem messages_source_residual (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (precision : ℕ) (hp : 1 ≤ precision) (κ : ℝ) (η : ℚ)
    (hκ : 1 ≤ κ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hcondition : (S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S) ≤ κ)
    (hprecision : (S.nnz : ℝ)/(2*2^precision) ≤ (η : ℝ)/(64*κ))
    (w : SourceDecoration.Vertex S precision → ℚ)
    (hres : ‖SourceSubdivision.operator S precision
      (routedReadout S precision (rationalMomentVector w))-SourceSubdivision.source S precision‖ ≤
        (PhysicalAccuracy.epsilon S precision η : ℝ)*‖SourceSubdivision.source S precision‖/32) :
    Source.ResidualTarget S ((η : ℝ)/4) (sparseMomentDecode S precision w) := by
  apply SourceSubdivision.source_output_residual S hunit hm hb precision hp κ η
    hκ (by exact_mod_cast hη.le) (by exact_mod_cast hη1) hcondition hprecision
    (routedReadout S precision (rationalMomentVector w))
    (fun i => w (Sum.inl (SourceRouting.inputCoordinate S precision i)))
  · apply (mul_le_mul_of_nonneg_right (SourceRecovery.residualFactor_bound S precision)
      (norm_nonneg _)).trans
    apply (mul_le_mul_of_nonneg_left hres (by positivity)).trans
    have hbudget : (SourceRecovery.residualFactor S precision : ℝ)*
        (PhysicalAccuracy.epsilon S precision η : ℝ) ≤ (η : ℝ) := by
      exact_mod_cast PhysicalAccuracy.epsilon_residualFactor S precision η hη
    have hg := norm_nonneg (SourceSubdivision.source S precision)
    have he := mul_le_mul_of_nonneg_right hbudget hg
    have hηr : (0 : ℝ) ≤ η := by exact_mod_cast hη.le
    nlinarith only [he, mul_nonneg hηr hg]
  · intro i
    change |(w (Sum.inl (SourceRouting.inputCoordinate S precision i)) : ℝ)-
      (w (Sum.inl (SourceRouting.inputCoordinate S precision i)) : ℝ)| ≤ _
    rw [sub_self, abs_zero]
    positivity

#print axioms message_routed_residual
#print axioms messages_source_residual

end Maxwell.Continuum.FiniteAuxiliary
