import Maxwell.Continuum.FiniteAuxiliaryTemplateSource
import Maxwell.Continuum.FiniteAuxiliaryMessages
import Maxwell.Continuum.DyadicRounding

/-! The emitted source uses exactly one dyadic amplitude per original
sparse-source coordinate. The circuit, routing and mediator extensions
add no nonzero source amplitudes. -/

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition Maxwell.Logical ComplexInverse

def sourceAmplitude (S : Source.SparseSystem) (P : ℕ) (ĉ : ℚ) (i : Fin S.n) : Maxwell.Dyadic P :=
  roundDyadic P (ĉ*Normalization.normalizedSource S i)

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

local instance sourceAmplitudeSiteDecidableEq (S : Source.SparseSystem) (precision : ℕ) :
    DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

def sourceInputSite (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    SourceDecoration.Vertex S precision :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl ((sourceCircuit S precision).circuit.inputIndex i))))

theorem sourceInputSite_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (sourceInputSite S precision) := by
  intro i j h
  exact (sourceCircuit S precision).circuit.inputIndex_injective
    (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h))))

def originalComplexSource (S : Source.SparseSystem) : EuclideanSpace ℂ (Fin S.n) :=
  ofRealVector (Source.rationalVector (Normalization.normalizedSource S))

theorem originalComplexSource_norm (S : Source.SparseSystem) (precision : ℕ) :
    ‖originalComplexSource S‖ = ‖routedForcing S precision‖ := by
  rw [originalComplexSource, ofRealVector_norm, routedForcing_norm, SourceSubdivision.source_norm]

theorem routedForcing_sum_original (S : Source.SparseSystem) (precision : ℕ) :
    routedForcing S precision = ∑ i : Fin S.n,
      PiLp.single 2 (sourceInputSite S precision i) (originalComplexSource S i) := by
  classical
  apply PiLp.ext
  intro x
  rcases x with x | x
  · rcases x with x | x
    · rcases x with x | x
      · rcases x with x | x
        · change ((coordinateExtension (sourceCircuit S precision).circuit.inputIndex
            (Source.rationalVector (Normalization.normalizedSource S)) x : ℝ) : ℂ) = _
          rw [coordinateExtension_apply]
          simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply,
            sourceInputSite]
          rw [Complex.ofReal_sum]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : (sourceCircuit S precision).circuit.inputIndex i = x
          · subst x
            simp only [ite_true]
            rfl
          · have hne : ¬Sum.inl (Sum.inl (Sum.inl (Sum.inl x))) =
                sourceInputSite S precision i := by
              intro he
              exact hi (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj he)))).symm
            rw [ite_eq_right hi]
            exact (ite_eq_right hne).symm
        · change (0 : ℂ) = _
          simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply, sourceInputSite]
          symm
          apply Finset.sum_eq_zero
          intro i _
          exact ite_eq_right (by intro he; cases Sum.inl.inj (Sum.inl.inj (Sum.inl.inj he)))
      · change (0 : ℂ) = _
        simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply, sourceInputSite]
        symm
        apply Finset.sum_eq_zero
        intro i _
        exact ite_eq_right (by intro he; cases Sum.inl.inj (Sum.inl.inj he))
    · change (0 : ℂ) = _
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply, sourceInputSite]
      symm
      apply Finset.sum_eq_zero
      intro i _
      exact ite_eq_right (by intro he; cases Sum.inl.inj he)
  · change (0 : ℂ) = _
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply, sourceInputSite]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (by intro he; cases he)

def dyadicSourceVector (S : Source.SparseSystem) (P : ℕ) (ĉ : ℚ) : EuclideanSpace ℂ (Fin S.n) :=
  WithLp.toLp 2 fun i => (((sourceAmplitude S P ĉ i).value : ℝ) : ℂ)

theorem dyadicSourceVector_error (S : Source.SparseSystem) (P : ℕ) (ĉ : ℚ) :
    ‖dyadicSourceVector S P ĉ-(ĉ : ℂ) • originalComplexSource S‖ ≤
      (S.n : ℝ)*(1/2 : ℝ)^P := by
  apply (euclidean_norm_le_sum_norm _).trans
  calc
    _ ≤ ∑ _i : Fin S.n, (1/2 : ℝ)^P := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(((sourceAmplitude S P ĉ i).value : ℝ) : ℂ)-
        (ĉ : ℂ)*((Normalization.normalizedSource S i : ℝ) : ℂ)‖ ≤ _
      change ‖(((sourceAmplitude S P ĉ i).value : ℝ) : ℂ)-
        ((ĉ : ℝ) : ℂ)*((Normalization.normalizedSource S i : ℝ) : ℂ)‖ ≤ _
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simpa only [Rat.cast_mul, abs_sub_comm, sourceAmplitude] using
        roundDyadic_error P (ĉ*Normalization.normalizedSource S i)
    _ = _ := by simp

#print axioms sourceAmplitude
#print axioms routedForcing_sum_original
#print axioms dyadicSourceVector_error

end

end Maxwell.Continuum.FiniteAuxiliary
