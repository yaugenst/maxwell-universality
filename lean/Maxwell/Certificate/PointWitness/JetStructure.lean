import Maxwell.Certificate.PointWitness.JetBounds
import Maxwell.Spectral.YeeCoefficientSymmetry
import Maxwell.Spectral.ClusterMixed
import Maxwell.Spectral.YeeLocal

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.YeeTaylor
noncomputable section

theorem pointEffectiveCoefficient_selfAdjoint (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) : IsSelfAdjoint (pointEffectiveCoefficient hgap q) := by
  apply ClusterMixed.effective_selfAdjoint (pointTaylorCoefficient q 0)
    (pointTaylorCoefficient q 1) (pointTaylorCoefficient q 2)
  · exact shiftedOperatorCoefficient_selfAdjoint _ _ _ _ 0 (by omega)
  · exact shiftedOperatorCoefficient_selfAdjoint _ _ _ _ 1 (by omega)
  · exact shiftedOperatorCoefficient_selfAdjoint _ _ _ _ 2 (by omega)
  · exact pointCorrector_equation hgap q

theorem pointEffectiveCoefficient_norm_le (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum)
    (hforms : ∀ x, radius q^2 * ‖x‖^2 / 50 ≤
        Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ∧
      Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ≤ radius q^2 * ‖x‖^2) :
    ‖pointEffectiveCoefficient hgap q‖ ≤ radius q^2 := by
  apply ClusterMixed.effective_norm_le _ (pointEffectiveCoefficient_selfAdjoint hgap q)
    _ (sq_nonneg _)
  · intro x
    exact (by positivity : (0 : ℝ) ≤ radius q^2 * ‖x‖^2 / 50).trans (hforms x).1
  · exact fun x => (hforms x).2

theorem pointMixedOffset_bound (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum)
    (hK : ‖pointEffectiveCoefficient hgap q‖ ≤ radius q^2)
    (x : EuclideanSpace ℂ (Fin 2)) :
    Complex.re (inner ℂ ((pointTaylorCoefficient q 0).comp
        (pointExactIsometry hgap).toContinuousLinearMap x)
      (residualTaylorTerm (pointTaylorCoefficient q)
        (pointExactIsometry hgap).toContinuousLinearMap (pointCorrector hgap q) 1 x)) ≤
      pointClusterWidth * radius q^2 * ‖x‖^2 := by
  have hzero : pointTaylorCoefficient q 0 = pointShiftedOperator pointEnergy :=
    pointShiftedOperator_eq_coefficient q pointEnergy
  apply ClusterMixed.mixed_offset_bound
    (pointExactIsometry hgap).toContinuousLinearMap _ _ pointClusterWidth (radius q^2)
    pointClusterWidth_bounds.1.le (pointExactIsometry hgap).norm_toContinuousLinearMap_le
  · rw [hzero]
    exact (pointExactIsometry_center_bounds hgap).1
  · simpa only [residualTaylorTerm, ContinuousLinearMap.comp_sub, pointEffectiveCoefficient,
      show (1:ℕ)+1=2 by omega] using hK
  · rw [hzero]
    exact pointShiftedOperator_exactFrame_invariant hgap pointEnergy

/-- All structural finite-jet fields are discharged for the actual exact
frame and corrector. Only the quadratic form and full residual-Gram
inequalities require the remaining finite derivative certificates. -/
theorem pointFiniteJetBounds (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum)
    (hforms : ∀ x, radius q^2 * ‖x‖^2 / 50 ≤
        Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ∧
      Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ≤ radius q^2 * ‖x‖^2)
    (hresidual : ∀ x, ‖residualTaylorTerm (pointTaylorCoefficient q)
        (pointExactIsometry hgap).toContinuousLinearMap (pointCorrector hgap q) 1 x‖^2 ≤
      (18/5 : ℝ) * radius q^2 * Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x))) :
    FiniteJetBounds (pointTaylorCoefficient q) (pointExactIsometry hgap).toContinuousLinearMap
      (pointCorrector hgap q) (radius q) pointClusterWidth pointEnergy := by
  have hzero : pointTaylorCoefficient q 0 = pointShiftedOperator pointEnergy :=
    pointShiftedOperator_eq_coefficient q pointEnergy
  refine ⟨?_, fun x => (hforms x).1, fun x => (hforms x).2, hresidual, ?_, ?_⟩
  · rw [hzero]
    exact (pointExactIsometry_center_bounds hgap).1
  · exact pointMixedOffset_bound hgap q (pointEffectiveCoefficient_norm_le hgap q hforms)
  · rw [hzero]
    exact (pointExactIsometry_center_bounds hgap).2

theorem point_local_band_gap (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum)
    (hr0 : 0 < radius q) (hr : radius q ≤ 1/20)
    (hforms : ∀ x, radius q^2 * ‖x‖^2 / 50 ≤
        Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ∧
      Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)) ≤ radius q^2 * ‖x‖^2)
    (hresidual : ∀ x, ‖residualTaylorTerm (pointTaylorCoefficient q)
        (pointExactIsometry hgap).toContinuousLinearMap (pointCorrector hgap q) 1 x‖^2 ≤
      (18/5 : ℝ) * radius q^2 * Complex.re (inner ℂ x (pointEffectiveCoefficient hgap q x)))
    (hinertia : (Finset.univ.filter fun i =>
      0 < (YeeTaylorRemainder.centeredOperator_symmetric ![1,1,0] q).eigenvalues rfl i ∧
      (YeeTaylorRemainder.centeredOperator_symmetric ![1,1,0] q).eigenvalues rfl i < 7/256).card ≤ 2) :
    ∀ i : Fin (Module.finrank ℂ PointSpace),
      0 < (YeeTaylorRemainder.centeredOperator_symmetric ![1,1,0] q).eigenvalues rfl i →
      (YeeTaylorRemainder.centeredOperator_symmetric ![1,1,0] q).eigenvalues rfl i < 7/256 →
      radius q^2 / 600 <
        (YeeTaylorRemainder.centeredOperator_symmetric ![1,1,0] q).eigenvalues rfl i - pointEnergy := by
  apply YeeLocal.local_band_gap ![1,1,0] q pointClusterWidth pointEnergy
    (pointExactIsometry hgap).toContinuousLinearMap (pointCorrector hgap q)
    hr0 hr pointClusterWidth_bounds.1.le pointClusterWidth_bounds.2
    pointEnergy_range.1 pointEnergy_range.2
    (pointExactIsometry hgap).norm_toContinuousLinearMap_le (pointCorrector_norm_le hgap q)
    (pointCorrector_equation hgap q) 1 (Or.inl rfl)
    (pointExactIsometry_even hgap) (pointCorrector_odd hgap q)
    (pointFiniteJetBounds hgap q hforms hresidual) _ hinertia
  simp

end
end Maxwell.Certificate.PointWitness
