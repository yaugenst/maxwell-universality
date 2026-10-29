import Maxwell.Certificate.PointWitness.ExactFrameInvariant
import Maxwell.Spectral.ClusterCenter

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

def pointEnergy : ℝ := pointOperator_symmetric.eigenvalues rfl pointIndex0

def pointClusterWidth : ℝ :=
  pointOperator_symmetric.eigenvalues rfl pointIndex1 - pointEnergy

theorem pointEnergy_range : 239 / 25000 ≤ pointEnergy ∧ pointEnergy ≤ 957 / 100000 := by
  have h := abs_le.mp pointIndex0_interval
  have hr := pointCenter0_range
  unfold pointEnergy
  constructor <;> linarith

theorem pointClusterWidth_bounds : 0 < pointClusterWidth ∧ pointClusterWidth ≤ 1 / 2^20 := by
  have h0 := abs_le.mp pointIndex0_interval
  have h1 := abs_le.mp pointIndex1_interval
  have hlo : pointCenter0 + 2 * ((1 : ℝ) / 2^47) < pointCenter1 := by
    norm_num [pointCenter0, pointCenter1, lambdaNumerator0, lambdaNumerator1]
  have hhi : pointCenter1 - pointCenter0 + 2 * ((1 : ℝ) / 2^47) ≤ 1 / 2^20 := by
    norm_num [pointCenter0, pointCenter1, lambdaNumerator0, lambdaNumerator1]
  unfold pointClusterWidth pointEnergy
  constructor <;> linarith

theorem pointCluster_window (i : PointIndex) (hi : i ∈ pointCluster) :
    0 ≤ pointOperator_symmetric.eigenvalues rfl i - pointEnergy ∧
      pointOperator_symmetric.eigenvalues rfl i - pointEnergy ≤ pointClusterWidth := by
  simp only [pointCluster, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · change 0 ≤ pointEnergy - pointEnergy ∧ pointEnergy - pointEnergy ≤ pointClusterWidth
    simpa only [sub_self, le_refl, true_and] using pointClusterWidth_bounds.1.le
  · exact ⟨pointClusterWidth_bounds.1.le, le_rfl⟩

theorem pointExactIsometry_spectral_support (hgap : PointClusterComplementGap)
    (x : EuclideanSpace ℂ (Fin 2)) (i : PointIndex)
    (hi : pointEigenbasis.repr (pointExactIsometry hgap x) i ≠ 0) : i ∈ pointCluster := by
  by_contra hnot
  have hfix := congrArg (fun L : EuclideanSpace ℂ (Fin 2) →L[ℂ] PointSpace => L x)
    (pointExactIsometry_projection hgap)
  change pointClusterProjection (pointExactIsometry hgap x) = pointExactIsometry hgap x at hfix
  have hc := congrArg (fun v : PointSpace => pointEigenbasis.repr v i) hfix
  change pointEigenbasis.repr
    (ClusterProjection.projection pointEigenbasis pointCluster (pointExactIsometry hgap x)) i = _ at hc
  rw [ClusterProjection.repr_projection, ite_eq_right hnot] at hc
  exact hi hc.symm

theorem pointContinuousOperator_symmetric : pointContinuousOperator.toLinearMap.IsSymmetric := by
  rw [pointContinuousOperator_toLinearMap]
  exact pointOperator_symmetric

/-- The center residual and center polynomial estimates of the local trial
lemma follow from the actual two-eigenvalue window and the constructed frame. -/
theorem pointExactIsometry_center_bounds (hgap : PointClusterComplementGap) :
    ‖(pointShiftedOperator pointEnergy).comp (pointExactIsometry hgap).toContinuousLinearMap‖ ≤
      pointClusterWidth ∧
    ∀ x, ‖(pointShiftedOperator pointEnergy).comp
        (pointExactIsometry hgap).toContinuousLinearMap x‖ ^ 2 ≤
      (7 / 256 - pointEnergy) * Complex.re (inner ℂ x
        ((pointExactIsometry hgap).toContinuousLinearMap.adjoint.comp
          ((pointShiftedOperator pointEnergy).comp
            (pointExactIsometry hgap).toContinuousLinearMap) x)) := by
  apply ClusterCenter.trial_center_bounds pointContinuousOperator pointContinuousOperator_symmetric
    (pointExactIsometry hgap).toContinuousLinearMap pointEnergy pointClusterWidth (7/256)
    pointClusterWidth_bounds.1.le
  · have hw := pointClusterWidth_bounds.2
    have he := pointEnergy_range.2
    norm_num at *
    linarith
  · exact (pointExactIsometry hgap).norm_toContinuousLinearMap_le
  · intro x i hi
    apply pointCluster_window i
    apply pointExactIsometry_spectral_support hgap x i
    exact hi

end
end Maxwell.Certificate.PointWitness
