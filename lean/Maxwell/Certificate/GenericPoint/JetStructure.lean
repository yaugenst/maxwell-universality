import Maxwell.Certificate.GenericPoint.JetBounds
import Maxwell.Spectral.YeeCoefficientSymmetry
import Maxwell.Spectral.ClusterMixed
import Maxwell.Spectral.YeeLocal

namespace Maxwell.Certificate.GenericPoint.Data
open Maxwell.Spectral Maxwell.Spectral.YeeTaylor
noncomputable section
variable (D : GenericPoint.Data)

theorem effectiveCoefficient_selfAdjoint (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) (q : PeriodicYee.Momentum) :
    IsSelfAdjoint (D.effectiveCoefficient hgap q) := by
  apply ClusterMixed.effective_selfAdjoint (D.taylorCoefficient q 0)
    (D.taylorCoefficient q 1) (D.taylorCoefficient q 2)
  · exact shiftedOperatorCoefficient_selfAdjoint _ _ _ _ 0 (by omega)
  · exact shiftedOperatorCoefficient_selfAdjoint _ _ _ _ 1 (by omega)
  · exact shiftedOperatorCoefficient_selfAdjoint _ _ _ _ 2 (by omega)
  · exact D.corrector_equation hgap σ hσ hv q

theorem effectiveCoefficient_norm_le (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) (q : PeriodicYee.Momentum)
    (hforms : ∀ x, radius q^2*‖x‖^2/50 ≤ Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x)) ∧
      Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x)) ≤ radius q^2*‖x‖^2) :
    ‖D.effectiveCoefficient hgap q‖ ≤ radius q^2 := by
  apply ClusterMixed.effective_norm_le _ (D.effectiveCoefficient_selfAdjoint hgap σ hσ hv q)
    _ (sq_nonneg _)
  · intro x
    exact (by positivity : (0:ℝ) ≤ radius q^2*‖x‖^2/50).trans (hforms x).1
  · exact fun x => (hforms x).2

theorem mixedOffset_bound (hgap : D.ComplementGap) (q : PeriodicYee.Momentum)
    (hwidth : D.width ≤ 7/256-D.energy)
    (hK : ‖D.effectiveCoefficient hgap q‖ ≤ radius q^2) (x : EuclideanSpace ℂ (Fin 2)) :
    Complex.re (inner ℂ ((D.taylorCoefficient q 0).comp
        (D.exactIsometry hgap).toContinuousLinearMap x)
      (residualTaylorTerm (D.taylorCoefficient q)
        (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q) 1 x)) ≤
      D.width*radius q^2*‖x‖^2 := by
  have hzero : D.taylorCoefficient q 0 = D.shiftedOperator D.energy :=
    D.shiftedOperator_eq_coefficient q D.energy
  apply ClusterMixed.mixed_offset_bound (D.exactIsometry hgap).toContinuousLinearMap _ _ D.width
    (radius q^2) D.width_pos.le (D.exactIsometry hgap).norm_toContinuousLinearMap_le
  · rw [hzero]
    exact (D.exactIsometry_center_bounds hgap (7/256) hwidth).1
  · simpa only [residualTaylorTerm,ContinuousLinearMap.comp_sub,effectiveCoefficient,
      show (1:ℕ)+1=2 by omega] using hK
  · rw [hzero]
    exact D.shiftedOperator_exactFrame_invariant hgap D.energy

theorem finiteJetBounds (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) (q : PeriodicYee.Momentum)
    (hwidth : D.width ≤ 7/256-D.energy)
    (hforms : ∀ x, radius q^2*‖x‖^2/50 ≤ Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x)) ∧
      Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x)) ≤ radius q^2*‖x‖^2)
    (hresidual : ∀ x, ‖residualTaylorTerm (D.taylorCoefficient q)
        (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q) 1 x‖^2 ≤
      (18/5:ℝ)*radius q^2*Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x))) :
    FiniteJetBounds (D.taylorCoefficient q) (D.exactIsometry hgap).toContinuousLinearMap
      (D.corrector hgap q) (radius q) D.width D.energy := by
  have hzero : D.taylorCoefficient q 0 = D.shiftedOperator D.energy :=
    D.shiftedOperator_eq_coefficient q D.energy
  refine ⟨?_,fun x => (hforms x).1,fun x => (hforms x).2,hresidual,?_,?_⟩
  · rw [hzero]
    exact (D.exactIsometry_center_bounds hgap (7/256) hwidth).1
  · exact D.mixedOffset_bound hgap q hwidth (D.effectiveCoefficient_norm_le hgap σ hσ hv q hforms)
  · rw [hzero]
    exact (D.exactIsometry_center_bounds hgap (7/256) hwidth).2

/-- The actual local Yee exclusion theorem for any canonical TRIM witness.
All analytic frame/corrector obligations are constructed above; the inputs
below are the finite curvature/Gram certificates and scalar interval checks. -/
theorem local_band_gap (hgap : D.ComplementGap) (σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hv : ∀ j, D.inversion (D.vector j) = σ • D.vector j) (q : PeriodicYee.Momentum)
    (hr0 : 0 < radius q) (hr : radius q ≤ 1/20)
    (hw : D.width ≤ 1/2^20) (hEl : 239/25000 ≤ D.energy) (hEu : D.energy ≤ 957/100000)
    (hY : ‖D.corrector hgap q‖ ≤ 3*radius q)
    (hforms : ∀ x, radius q^2*‖x‖^2/50 ≤ Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x)) ∧
      Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x)) ≤ radius q^2*‖x‖^2)
    (hresidual : ∀ x, ‖residualTaylorTerm (D.taylorCoefficient q)
        (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q) 1 x‖^2 ≤
      (18/5:ℝ)*radius q^2*Complex.re (inner ℂ x (D.effectiveCoefficient hgap q x)))
    (hinertia : (Finset.univ.filter fun i =>
      0 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i ∧
      (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i < 7/256).card ≤ 2) :
    ∀ i : Index, 0 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i →
      (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i < 7/256 →
      radius q^2/600 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i-D.energy := by
  have hwidth : D.width ≤ 7/256-D.energy := by linarith
  apply YeeLocal.local_band_gap D.k q D.width D.energy
    (D.exactIsometry hgap).toContinuousLinearMap (D.corrector hgap q)
    hr0 hr D.width_pos.le hw hEl hEu (D.exactIsometry hgap).norm_toContinuousLinearMap_le hY
    (D.corrector_equation hgap σ hσ hv q) σ hσ
    (D.exactIsometry_parity hgap σ hv) (D.corrector_parity hgap σ hσ hv q)
    (D.finiteJetBounds hgap σ hσ hv q hwidth hforms hresidual) _ hinertia
  simp

end
end Maxwell.Certificate.GenericPoint.Data
