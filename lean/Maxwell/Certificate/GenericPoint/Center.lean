import Maxwell.Certificate.GenericPoint.Invariant
import Maxwell.Spectral.ClusterCenter

namespace Maxwell.Certificate.GenericPoint.Data

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

variable (D : GenericPoint.Data)

def energy : ℝ := (operator_symmetric D.k).eigenvalues rfl (D.index 0)

def width : ℝ := (operator_symmetric D.k).eigenvalues rfl (D.index 1) - D.energy

theorem energy_close : |D.energy - D.center 0| ≤ D.residualRadius := D.interval 0

theorem energy_bounds : D.center 0 - D.residualRadius ≤ D.energy ∧
    D.energy ≤ D.center 0 + D.residualRadius := by
  have h := abs_le.mp D.energy_close
  constructor <;> linarith

theorem energy_range (lower upper : ℝ)
    (hl : lower ≤ D.center 0 - D.residualRadius)
    (hu : D.center 0 + D.residualRadius ≤ upper) :
    lower ≤ D.energy ∧ D.energy ≤ upper :=
  ⟨hl.trans D.energy_bounds.1, D.energy_bounds.2.trans hu⟩

theorem width_interval : |D.width - (D.center 1 - D.center 0)| ≤ 2 * D.residualRadius := by
  have h0 := abs_le.mp (D.interval 0)
  have h1 := abs_le.mp (D.interval 1)
  unfold width energy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem width_pos : 0 < D.width := by
  have h0 := abs_le.mp (D.interval 0)
  have h1 := abs_le.mp (D.interval 1)
  have hc := D.center_separated
  unfold width energy
  linarith

theorem width_bounds : 0 < D.width ∧
    D.width ≤ D.center 1 - D.center 0 + 2 * D.residualRadius := by
  refine ⟨D.width_pos, ?_⟩
  have h := (abs_le.mp D.width_interval).2
  linarith

theorem width_le (bound : ℝ)
    (h : D.center 1 - D.center 0 + 2 * D.residualRadius ≤ bound) : D.width ≤ bound :=
  D.width_bounds.2.trans h

theorem cluster_window (i : Index) (hi : i ∈ D.cluster) :
    0 ≤ (operator_symmetric D.k).eigenvalues rfl i - D.energy ∧
      (operator_symmetric D.k).eigenvalues rfl i - D.energy ≤ D.width := by
  simp only [cluster, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · change 0 ≤ D.energy - D.energy ∧ D.energy - D.energy ≤ D.width
    simpa only [sub_self, le_refl, true_and] using D.width_pos.le
  · exact ⟨D.width_pos.le, le_rfl⟩

theorem exactIsometry_spectral_support (hgap : D.ComplementGap)
    (x : EuclideanSpace ℂ (Fin 2)) (i : Index)
    (hi : D.eigenbasis.repr (D.exactIsometry hgap x) i ≠ 0) : i ∈ D.cluster := by
  by_contra hnot
  have hfix := congrArg (fun L : EuclideanSpace ℂ (Fin 2) →L[ℂ] Space => L x)
    (D.exactIsometry_projection hgap)
  change D.projection (D.exactIsometry hgap x) = D.exactIsometry hgap x at hfix
  have hc := congrArg (fun v : Space => D.eigenbasis.repr v i) hfix
  change D.eigenbasis.repr
    (ClusterProjection.projection D.eigenbasis D.cluster (D.exactIsometry hgap x)) i = _ at hc
  rw [ClusterProjection.repr_projection, ite_eq_right hnot] at hc
  exact hi hc.symm

theorem continuousOperator_symmetric : D.continuousOperator.toLinearMap.IsSymmetric := by
  rw [D.continuousOperator_toLinearMap]
  exact operator_symmetric D.k

/-- The actual two-eigenvalue window supplies the center residual and spectral
polynomial bounds for every admissible ceiling. -/
theorem exactIsometry_center_bounds (hgap : D.ComplementGap) (ceiling : ℝ)
    (hwidth : D.width ≤ ceiling - D.energy) :
    ‖(D.shiftedOperator D.energy).comp (D.exactIsometry hgap).toContinuousLinearMap‖ ≤
      D.width ∧
    ∀ x, ‖(D.shiftedOperator D.energy).comp
        (D.exactIsometry hgap).toContinuousLinearMap x‖ ^ 2 ≤
      (ceiling - D.energy) * Complex.re (inner ℂ x
        ((D.exactIsometry hgap).toContinuousLinearMap.adjoint.comp
          ((D.shiftedOperator D.energy).comp
            (D.exactIsometry hgap).toContinuousLinearMap) x)) := by
  apply ClusterCenter.trial_center_bounds D.continuousOperator D.continuousOperator_symmetric
    (D.exactIsometry hgap).toContinuousLinearMap D.energy D.width ceiling
    D.width_pos.le hwidth
  · exact (D.exactIsometry hgap).norm_toContinuousLinearMap_le
  · intro x i hi
    apply D.cluster_window i
    apply D.exactIsometry_spectral_support hgap x i
    exact hi

end
end Maxwell.Certificate.GenericPoint.Data
