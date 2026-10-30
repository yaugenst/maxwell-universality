import Maxwell.Continuum.FiniteAuxiliaryMediatorRecovery
import Maxwell.Composition.SourceMediator

/-! The actual sparse right-hand side, including zero coordinates for
all routing and mediator vertices. Its coefficient sum depends on the
original source dimension, not on the total number of physical wells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition Maxwell.Logical ComplexInverse

theorem sum_norm_leftInjection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : EuclideanSpace ℝ ι) :
    (∑ i, ‖sumLeftInjection (κ := κ) g i‖) = ∑ i, ‖g i‖ := by
  simp only [Fintype.sum_sum_type, sumLeftInjection_inl, sumLeftInjection_inr,
    norm_zero, Finset.sum_const_zero, add_zero]

theorem sum_norm_coordinateExtension_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (pick : κ → ι) (g : EuclideanSpace ℝ κ) :
    (∑ i, ‖coordinateExtension pick g i‖) ≤ ∑ i, ‖g i‖ := by
  calc
    _ ≤ ∑ i, ∑ j, ‖if pick j = i then g j else 0‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [coordinateExtension_apply]
      exact norm_sum_le _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      have he (i : ι) : ‖if pick j = i then g j else 0‖ = if pick j = i then ‖g j‖ else 0 := by
        split_ifs <;> simp
      simp only [he]
      simp

def routedForcing (S : Source.SparseSystem) (precision : ℕ) :
    EuclideanSpace ℂ (SourceDecoration.Vertex S precision) :=
  complexTerminalInjection (ofRealVector (SourceSubdivision.source S precision))

theorem routedForcing_norm (S : Source.SparseSystem) (precision : ℕ) :
    ‖routedForcing S precision‖ = ‖SourceSubdivision.source S precision‖ := by
  rw [routedForcing, complexTerminalInjection_norm, ofRealVector_norm]

theorem routedForcing_norm_bounds (S : Source.SparseSystem) (hb : S.source ≠ 0) (precision : ℕ) :
    1 ≤ ‖routedForcing S precision‖ ∧ ‖routedForcing S precision‖ ≤ Real.sqrt (S.n : ℝ) := by
  rw [routedForcing_norm]
  exact SourceSubdivision.source_norm_bounds S hb precision

theorem routedForcing_sum (S : Source.SparseSystem) (precision : ℕ) :
    (∑ i, ‖routedForcing S precision i‖) ≤ (S.n : ℝ)*‖routedForcing S precision‖ := by
  classical
  have hinj : (∑ i, ‖SourceSubdivision.source S precision i‖) ≤
      ∑ i, ‖Source.rationalVector (Normalization.normalizedSource S) i‖ := by
    change (∑ i : SourcePositive.Vertex S precision ⊕ SubdivisionSchur.Internal (SourceRouting.data S precision),
      ‖sumLeftInjection (PositiveRecovery.source S precision) i‖) ≤ _
    rw [sum_norm_leftInjection, PositiveRecovery.source]
    change (∑ i, ‖sumLeftInjection (sumLeftInjection
      (SourceResidual.sourceBoundary S precision
        (Source.rationalVector (Normalization.normalizedSource S)))) i‖) ≤ _
    rw [sum_norm_leftInjection, sum_norm_leftInjection]
    exact sum_norm_coordinateExtension_le _ _
  have hs : (∑ i, ‖routedForcing S precision i‖) = ∑ i, ‖SourceSubdivision.source S precision i‖ := by
    simp only [routedForcing, complexTerminalInjection, Fintype.sum_sum_type,
      WithLp.ofLp_toLp, Sum.elim_inl, Sum.elim_inr, norm_zero, Finset.sum_const_zero,
      add_zero, ofRealVector, Complex.norm_real]
  rw [hs, routedForcing_norm, SourceSubdivision.source_norm]
  apply hinj.trans
  calc
    _ ≤ ∑ _i : Fin S.n, ‖Source.rationalVector (Normalization.normalizedSource S)‖ :=
      Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
    _ = _ := by simp

theorem routedForcing_sum_le_nnz (S : Source.SparseSystem) (precision : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) :
    (∑ i, ‖routedForcing S precision i‖) ≤ (S.nnz : ℝ)*‖routedForcing S precision‖ := by
  apply (routedForcing_sum S precision).trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast Source.dimension_le_nnz S hunit) (norm_nonneg _)

theorem realPart_norm_le {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) :
    ‖ComplexInverse.realPart x‖ ≤ ‖x‖ := by
  have he := norm_sq_parts x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith only [he, sq_nonneg ‖imagPart x‖]

#print axioms routedForcing_sum_le_nnz

end Maxwell.Continuum.FiniteAuxiliary
