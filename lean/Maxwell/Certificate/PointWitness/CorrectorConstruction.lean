import Maxwell.Certificate.PointWitness.ExactFrameParity
import Maxwell.Certificate.PointWitness.ExactFrameInvariant
import Maxwell.Certificate.PointWitness.CenterBounds
import Maxwell.Spectral.ClusterParity
import Maxwell.Spectral.JetTransfer

/-! The exact corrector of the actual point spectral frame. The gap is
translated from the rational certificate center to the actual eigenvalue,
retaining the full `2⁻⁴⁷` loss before constructing the reduced inverse. -/

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

def pointEnergyGap : ℝ := 11 / 2000 - 1 / 2^47

theorem pointEnergyGap_pos : 0 < pointEnergyGap := by norm_num [pointEnergyGap]

theorem pointEnergy_close : |pointEnergy - pointCenter0| ≤ 1 / 2^47 :=
  pointIndex0_interval

theorem pointEnergy_complement_gap (hgap : PointClusterComplementGap)
    (i : PointIndex) (hi : i ∉ pointCluster) :
    pointEnergyGap ≤ |pointOperator_symmetric.eigenvalues rfl i - pointEnergy| := by
  have hg := hgap i hi 0
  change 11 / 2000 ≤ |pointOperator_symmetric.eigenvalues rfl i - pointCenter0| at hg
  have ht := abs_sub_le (pointOperator_symmetric.eigenvalues rfl i) pointEnergy pointCenter0
  have he := pointEnergy_close
  unfold pointEnergyGap
  linarith

theorem pointEnergy_complement_ne (hgap : PointClusterComplementGap)
    (i : PointIndex) (hi : i ∉ pointCluster) :
    pointOperator_symmetric.eigenvalues rfl i ≠ pointEnergy := by
  intro heq
  have hg := pointEnergy_complement_gap hgap i hi
  rw [heq, sub_self, abs_zero] at hg
  exact (not_le_of_gt pointEnergyGap_pos) hg

def pointReducedInverse : PointSpace →L[ℂ] PointSpace :=
  ClusterInverse.reducedInverse pointEigenbasis (pointOperator_symmetric.eigenvalues rfl)
    pointCluster pointEnergy

theorem pointReducedInverse_norm_le (hgap : PointClusterComplementGap) :
    ‖pointReducedInverse‖ ≤ pointEnergyGap⁻¹ :=
  ClusterInverse.reducedInverse_norm_le pointEigenbasis pointOperator
    (pointOperator_symmetric.eigenvalues rfl)
    (pointOperator_symmetric.eigenvectorBasis_apply_self_apply rfl)
    pointCluster pointEnergy pointEnergyGap pointEnergyGap_pos
    (pointEnergy_complement_gap hgap)

def pointTaylorCoefficient (q : PeriodicYee.Momentum) (n : ℕ) :
    PointSpace →L[ℂ] PointSpace :=
  YeeTaylor.shiftedOperatorCoefficient Concrete.material
    (timeReversalMomentum ![1,1,0]) q pointEnergy n

def pointFirstOrderRhs (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace :=
  (pointTaylorCoefficient q 1).comp (pointExactIsometry hgap).toContinuousLinearMap

theorem pointTaylorCoefficient_first_norm (q : PeriodicYee.Momentum) :
    ‖pointTaylorCoefficient q 1‖ ≤ (11/5 : ℝ) * YeeTaylor.radius q := by
  have h := YeeTaylor.shiftedOperatorCoefficient_norm_le Concrete.material
    (timeReversalMomentum ![1,1,0]) q pointEnergy 1 (by omega)
  have hc : taylorCoefficientMajorant 1 = (11/5 : ℝ) := by
    norm_num [taylorCoefficientMajorant]
  simpa only [pointTaylorCoefficient, hc, pow_one] using h

def pointCorrector (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace :=
  pointReducedInverse.comp (pointFirstOrderRhs hgap q)

theorem pointFirstOrderRhs_odd (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum) :
    HasParity pointInversion (-1) (pointFirstOrderRhs hgap q) := by
  have h := (pointExactIsometry_even hgap).odd_comp (pointTaylorCoefficient q)
    (YeeInversion.shiftedOperator_taylorParity ![1,1,0] q pointEnergy) 0
  exact h

theorem pointOdd_projection_zero (hgap : PointClusterComplementGap)
    (x : PointSpace) (hx : pointInversion x = (-1 : ℂ) • x) :
    pointClusterProjection x = 0 :=
  ClusterInverse.projection_zero_of_opposite_parity pointEigenbasis pointCluster
    pointInversion 1 (Or.inl rfl)
    (fun i hi => by simpa only [one_smul] using pointCluster_eigenbasis_even hgap i hi) x hx

theorem pointFirstOrderRhs_projection_zero (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    pointClusterProjection (pointFirstOrderRhs hgap q x) = 0 :=
  pointOdd_projection_zero hgap _ (pointFirstOrderRhs_odd hgap q x)

/-- The exact physical first-order corrector equation, with no residual
or equation supplied as a hypothesis. -/
theorem pointCorrector_equation (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum) :
    (pointTaylorCoefficient q 0).comp (pointCorrector hgap q) =
      (pointTaylorCoefficient q 1).comp (pointExactIsometry hgap).toContinuousLinearMap := by
  change (YeeTaylor.shiftedOperatorCoefficient Concrete.material
    (timeReversalMomentum ![1,1,0]) q pointEnergy 0).comp _ = _
  rw [pointShiftedOperator_eq_coefficient]
  apply ContinuousLinearMap.ext
  intro x
  have h := ClusterInverse.solve_complement pointEigenbasis pointOperator
    (pointOperator_symmetric.eigenvalues rfl)
    (pointOperator_symmetric.eigenvectorBasis_apply_self_apply rfl)
    pointCluster pointEnergy (pointEnergy_complement_ne hgap)
    (pointFirstOrderRhs hgap q x) (pointFirstOrderRhs_projection_zero hgap q x)
  change pointContinuousOperator (pointCorrector hgap q x) -
    (pointEnergy : ℂ) • pointCorrector hgap q x = pointFirstOrderRhs hgap q x
  have he := LinearMap.congr_fun pointContinuousOperator_toLinearMap (pointCorrector hgap q x)
  change pointContinuousOperator (pointCorrector hgap q x) =
    pointOperator (pointCorrector hgap q x) at he
  rw [he]
  exact h

theorem pointCorrector_odd (hgap : PointClusterComplementGap) (q : PeriodicYee.Momentum) :
    HasParity pointInversion (-1) (pointCorrector hgap q) := by
  intro x
  exact ClusterInverse.reducedInverse_opposite_parity pointEigenbasis pointOperator
    (pointOperator_symmetric.eigenvalues rfl)
    (pointOperator_symmetric.eigenvectorBasis_apply_self_apply rfl)
    pointCluster pointEnergy pointEnergyGap pointEnergyGap_pos
    (pointEnergy_complement_gap hgap) pointInversion 1 (Or.inl rfl)
    (fun i hi => by simpa only [one_smul] using pointCluster_eigenbasis_even hgap i hi)
    pointOperator_commutes_inversion (pointFirstOrderRhs hgap q x)
    (pointFirstOrderRhs_odd hgap q x)

theorem pointCorrector_projection_zero (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (x : EuclideanSpace ℂ (Fin 2)) :
    pointClusterProjection (pointCorrector hgap q x) = 0 :=
  pointOdd_projection_zero hgap _ (pointCorrector_odd hgap q x)

/-- Any checked odd saved corrector is compared to the constructed exact one
by its actual shifted residual and the energy-centered complement gap. -/
theorem pointCorrector_saved_error (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace)
    (hY : HasParity pointInversion (-1) savedY) :
    ‖pointCorrector hgap q - savedY‖ ≤
      ‖pointFirstOrderRhs hgap q - (pointShiftedOperator pointEnergy).comp savedY‖ /
        pointEnergyGap := by
  apply ClusterInverse.corrector_error_opNorm pointEigenbasis pointContinuousOperator
    (pointOperator_symmetric.eigenvalues rfl)
    (pointOperator_symmetric.eigenvectorBasis_apply_self_apply rfl)
    pointCluster pointEnergy pointEnergyGap pointEnergyGap_pos
    (pointEnergy_complement_gap hgap) (pointFirstOrderRhs hgap q) savedY
  intro x
  exact pointOdd_projection_zero hgap _ (hY x)

def pointSavedCorrectorResidual (q : PeriodicYee.Momentum)
    (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace :=
  (pointShiftedOperator pointCenter0).comp savedY -
    (pointTaylorCoefficient q 1).comp pointReferenceMap

/-- Replacement accounts explicitly for both the rounded energy and the
literal approximate frame. Only the saved residual and saved norm remain to
be supplied by their finite exact checks. -/
theorem pointCorrector_saved_error_reference (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace)
    (hY : HasParity pointInversion (-1) savedY) :
    ‖pointCorrector hgap q - savedY‖ ≤
      (‖pointSavedCorrectorResidual q savedY‖ + ((1 : ℝ) / 2^47) * ‖savedY‖ +
        ‖pointTaylorCoefficient q 1‖ * (1 / 10000000000)) / pointEnergyGap := by
  apply (pointCorrector_saved_error hgap q savedY hY).trans
  apply div_le_div_of_nonneg_right _ pointEnergyGap_pos.le
  have ht := JetTransfer.corrector_residual_transport pointContinuousOperator
    (pointTaylorCoefficient q 1) (pointExactIsometry hgap).toContinuousLinearMap
    pointReferenceMap savedY pointEnergy pointCenter0
  have he : |pointCenter0 - pointEnergy| ≤ (1 : ℝ) / 2^47 := by
    simpa only [abs_sub_comm] using pointEnergy_close
  have hf : ‖pointReferenceMap - (pointExactIsometry hgap).toContinuousLinearMap‖ ≤
      (1 : ℝ) / 10000000000 := by
    simpa only [norm_sub_rev] using (pointExactIsometry_close hgap).le
  change ‖pointFirstOrderRhs hgap q - (pointShiftedOperator pointEnergy).comp savedY‖ ≤ _
  calc
    _ ≤ ‖pointSavedCorrectorResidual q savedY‖ + |pointCenter0 - pointEnergy| * ‖savedY‖ +
        ‖pointTaylorCoefficient q 1‖ *
          ‖pointReferenceMap - (pointExactIsometry hgap).toContinuousLinearMap‖ := by
      calc
        _ = ‖(pointShiftedOperator pointEnergy).comp savedY - pointFirstOrderRhs hgap q‖ :=
          norm_sub_rev _ _
        _ ≤ _ := ht
    _ ≤ _ := add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right he (norm_nonneg _)))
      (mul_le_mul_of_nonneg_left hf (norm_nonneg _))

theorem pointCorrector_error_of_saved_bounds (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace)
    (hY : HasParity pointInversion (-1) savedY)
    (hnorm : ‖savedY‖ ≤ (2909/1000 : ℝ) * YeeTaylor.radius q)
    (hresidual : ‖pointSavedCorrectorResidual q savedY‖ ≤
      (1/100000000000 : ℝ) * YeeTaylor.radius q) :
    ‖pointCorrector hgap q - savedY‖ ≤ ((1 : ℝ) / 2^24) * YeeTaylor.radius q := by
  apply (pointCorrector_saved_error_reference hgap q savedY hY).trans
  apply (div_le_iff₀ pointEnergyGap_pos).mpr
  have hYn := mul_le_mul_of_nonneg_left hnorm (by positivity : (0 : ℝ) ≤ 1/2^47)
  have hA := mul_le_mul_of_nonneg_right (pointTaylorCoefficient_first_norm q)
    (by norm_num : (0 : ℝ) ≤ 1/10000000000)
  unfold pointEnergyGap
  nlinarith only [hresidual, hYn, hA, YeeTaylor.radius_nonneg q]

/-- The finite saved norm and residual budgets imply the manuscript's true
exact-corrector norm bound. -/
theorem pointCorrector_norm_of_saved_bounds (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) (savedY : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace)
    (hY : HasParity pointInversion (-1) savedY)
    (hnorm : ‖savedY‖ ≤ (2909/1000 : ℝ) * YeeTaylor.radius q)
    (hresidual : ‖pointSavedCorrectorResidual q savedY‖ ≤
      (1/100000000000 : ℝ) * YeeTaylor.radius q) :
    ‖pointCorrector hgap q‖ ≤ 3 * YeeTaylor.radius q := by
  have he := pointCorrector_error_of_saved_bounds hgap q savedY hY hnorm hresidual
  have ht := norm_le_norm_sub_add (pointCorrector hgap q) savedY
  nlinarith only [he, ht, hnorm, YeeTaylor.radius_nonneg q]

end
end Maxwell.Certificate.PointWitness
