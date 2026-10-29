import Maxwell.Continuum.PlacementConstants

/-! The integer placement lattice is within one percent of the actual
Euclidean metric induced by the continuum Hessian. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

def realPlacementMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun j => (placementDiagonal j : ℝ))

def inverseSqrtHessian : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun j => (Real.sqrt (hessian j j))⁻¹)

theorem realPlacementMatrix_eq_cast :
    realPlacementMatrix = placementMatrix.map (Int.castRingHom ℝ) := by
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [realPlacementMatrix, placementMatrix]
  · simp [realPlacementMatrix, placementMatrix, Matrix.diagonal_apply_ne _ hjk]

theorem inverseSqrtHessian_coordinate (j : Fin 3) :
    (inverseSqrtHessian j j)^2 * hessian j j = 1 := by
  simp only [inverseSqrtHessian, Matrix.diagonal_apply_eq, inv_pow,
    Real.sq_sqrt (hessian_diagonal_positive j).le]
  exact inv_mul_cancel₀ (hessian_diagonal_positive j).ne'

theorem inverseSqrtHessian_sandwich :
    inverseSqrtHessian * hessian * inverseSqrtHessian = 1 := by
  have hd : hessian = Matrix.diagonal (fun j => hessian j j) := by
    ext j k
    by_cases hjk : j = k
    · subst k; simp
    · simp [hessian, hjk]
  rw [hd, inverseSqrtHessian, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext j k
  by_cases hjk : j = k
  · subst k
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    have h := inverseSqrtHessian_coordinate j
    simp only [inverseSqrtHessian, Matrix.diagonal_apply_eq] at h
    nlinarith
  · simp [Matrix.diagonal_apply_ne _ hjk, Matrix.one_apply_ne hjk]

def placementInHessianMetric : Space →L[ℝ] Space :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) (inverseSqrtHessian * realPlacementMatrix)

theorem placementInHessianMetric_apply (v : Space) (j : Fin 3) :
    placementInHessianMetric v j =
      ((placementDiagonal j : ℝ) / Real.sqrt (hessian j j)) * v j := by
  change ((inverseSqrtHessian * realPlacementMatrix).mulVec v.ofLp) j = _
  rw [← Matrix.mulVec_mulVec]
  simp only [inverseSqrtHessian, realPlacementMatrix, Matrix.mulVec_diagonal]
  ring

theorem placement_ratio_bounds (j : Fin 3) :
    (99 / 100 : ℝ)^2 ≤ (placementDiagonal j : ℝ)^2 / hessian j j ∧
      (placementDiagonal j : ℝ)^2 / hessian j j ≤ (101 / 100 : ℝ)^2 := by
  constructor
  · exact (le_div_iff₀ (hessian_diagonal_positive j)).mpr (placement_diagonal_squared j).1
  · exact (div_le_iff₀ (hessian_diagonal_positive j)).mpr (placement_diagonal_squared j).2

theorem placementInHessianMetric_norm_sq (v : Space) :
    ‖placementInHessianMetric v‖^2 =
      ∑ j, ((placementDiagonal j : ℝ)^2 / hessian j j) * (v j)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [placementInHessianMetric_apply]
  simp only [Real.norm_eq_abs, sq_abs, mul_pow, div_pow,
    Real.sq_sqrt (hessian_diagonal_positive j).le]

theorem placement_metric_squared (v : Space) :
    (99 / 100 : ℝ)^2 * ‖v‖^2 ≤ ‖placementInHessianMetric v‖^2 ∧
      ‖placementInHessianMetric v‖^2 ≤ (101 / 100 : ℝ)^2 * ‖v‖^2 := by
  rw [placementInHessianMetric_norm_sq, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (placement_ratio_bounds j).1 (sq_nonneg _)
  · exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (placement_ratio_bounds j).2 (sq_nonneg _)

/-- The stated physical metric inequality for the literal integer matrix B. -/
theorem placement_metric (v : Space) :
    (99 / 100 : ℝ) * ‖v‖ ≤ ‖placementInHessianMetric v‖ ∧
      ‖placementInHessianMetric v‖ ≤ (101 / 100 : ℝ) * ‖v‖ := by
  obtain ⟨hlo, hhi⟩ := placement_metric_squared v
  constructor <;> nlinarith [norm_nonneg v, norm_nonneg (placementInHessianMetric v)]

end Maxwell.Continuum.PeriodicBand
