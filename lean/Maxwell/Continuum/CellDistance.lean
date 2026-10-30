import Maxwell.Continuum.CellSpatialBoundary
import Maxwell.Continuum.PeriodicTubeShift
import Maxwell.Continuum.MasterConstants

/-! Literal distance between the paper's half-open period cells, and
the Euclidean rate implied by the actual Hessian metric. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Bloch PeriodicBand MasterConstants

attribute [local irreducible] hessian

/-- The distance from zero to the set of differences is the infimum of
the distances between points in the two actual half-open cells. -/
def paperCellDistance (a b : Bloch.Alias) : ℝ :=
  Metric.infDist (0 : Space) {r | ∃ x ∈ paperBox a, ∃ y ∈ paperBox b, r = x-y}

theorem latticeShift_mem_paperBox (a : Bloch.Alias) : latticeShift a ∈ paperBox a := by
  intro j
  change 2*(a j : ℝ) ≤ 2*(a j : ℝ) ∧ 2*(a j : ℝ) < 2*(a j : ℝ)+2
  constructor <;> linarith

theorem paperCellDistance_nonneg (a b : Bloch.Alias) : 0 ≤ paperCellDistance a b :=
  Metric.infDist_nonneg

theorem paperCellDistance_le_pair {a b : Bloch.Alias} {x y : Space}
    (hx : x ∈ paperBox a) (hy : y ∈ paperBox b) : paperCellDistance a b ≤ dist x y := by
  have hd := Metric.infDist_le_dist_of_mem (x := (0 : Space))
    (s := {r | ∃ x ∈ paperBox a, ∃ y ∈ paperBox b, r = x-y})
    (show x-y ∈ {r | ∃ x ∈ paperBox a, ∃ y ∈ paperBox b, r = x-y} from ⟨x,hx,y,hy,rfl⟩)
  simpa only [paperCellDistance, dist_eq_norm, zero_sub, norm_neg] using hd

theorem paperCellDistance_le_center (a b : Bloch.Alias) :
    paperCellDistance a b ≤ ‖latticeShift a-latticeShift b‖ := by
  simpa only [dist_eq_norm] using
    paperCellDistance_le_pair (latticeShift_mem_paperBox a) (latticeShift_mem_paperBox b)

theorem hessian_diagonal_upper (j : Fin 3) : hessian j j ≤ (2 : ℝ)^110 := by
  have h := (hessian_bounds (Pi.single j 1)).2
  have hd : dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1) = 1 := by
    simp [dotProduct, Pi.single_apply]
  have hq : dotProduct (Pi.single j (1 : ℝ)) (hessian.mulVec (Pi.single j 1)) =
      hessian j j := by simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [hd, hq, mul_one] at h
  exact h.trans (by norm_num [FreeFiber.backgroundAmplitude])

theorem norm_sq_le_dual_energy (R : Space) :
    ‖R‖^2 ≤ (2 : ℝ)^110 * dualHessianEnergy R.ofLp := by
  rw [EuclideanSpace.norm_sq_eq, dualHessianEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change ‖R j‖^2 ≤ (2 : ℝ)^110 * ((R j)^2 / hessian j j)
  rw [Real.norm_eq_abs, sq_abs, ← mul_div_assoc]
  apply (le_div_iff₀ (hessian_diagonal_positive j)).mpr
  nlinarith [mul_le_mul_of_nonneg_right (hessian_diagonal_upper j) (sq_nonneg (R j))]

theorem hessianMetric_euclidean_rate (R : Space) :
    cs * ‖R‖ ≤ (99/100 : ℝ) * dualHessianDistance R.ofLp := by
  have hc : cs^2 * (2 : ℝ)^110 ≤ (99/100 : ℝ)^2 := by norm_num [cs]
  have hsq : (cs * ‖R‖)^2 ≤ ((99/100 : ℝ) * dualHessianDistance R.ofLp)^2 := by
    rw [mul_pow, mul_pow, dualHessianDistance_sq]
    calc
      _ ≤ cs^2 * ((2 : ℝ)^110 * dualHessianEnergy R.ofLp) :=
        mul_le_mul_of_nonneg_left (norm_sq_le_dual_energy R) (sq_nonneg cs)
      _ = (cs^2 * (2 : ℝ)^110) * dualHessianEnergy R.ofLp := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (dualHessianEnergy_nonneg _)
  exact (sq_le_sq₀ (mul_nonneg cs_pos.le (norm_nonneg R))
    (mul_nonneg (by norm_num) (dualHessianDistance_nonneg _))).mp hsq

theorem paperCellDistance_metric_rate (a b : Bloch.Alias) :
    cs * paperCellDistance a b ≤
      (99/100 : ℝ) * dualHessianDistance (latticeShift a-latticeShift b).ofLp :=
  (mul_le_mul_of_nonneg_left (paperCellDistance_le_center a b) cs_pos.le).trans
    (hessianMetric_euclidean_rate _)

#print axioms paperCellDistance_metric_rate

end Maxwell.Continuum.CellGauge
