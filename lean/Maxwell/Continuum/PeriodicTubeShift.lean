import Maxwell.Continuum.PeriodicTubeCellSymbol
import Maxwell.Continuum.PlacementMetric

/-! The literal optimal imaginary displacement for the Hessian metric.
The zero displacement is included, using the usual total real division. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary

def inverseHessianVector (R : Corner.Vec) : Corner.Vec := fun j => R j / hessian j j

def dualHessianEnergy (R : Corner.Vec) : ℝ :=
  ∑ j : Fin 3, (R j)^2 / hessian j j

def dualHessianDistance (R : Corner.Vec) : ℝ := Real.sqrt (dualHessianEnergy R)

def optimalTubeShift (h : ℝ) (R : Corner.Vec) : Corner.Vec :=
  ((99 / 100 : ℝ) * h / dualHessianDistance R) • inverseHessianVector R

theorem dualHessianEnergy_nonneg (R : Corner.Vec) : 0 ≤ dualHessianEnergy R :=
  Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hessian_diagonal_positive j).le)

theorem dualHessianDistance_nonneg (R : Corner.Vec) : 0 ≤ dualHessianDistance R :=
  Real.sqrt_nonneg _

theorem dualHessianDistance_sq (R : Corner.Vec) :
    dualHessianDistance R ^ 2 = dualHessianEnergy R :=
  Real.sq_sqrt (dualHessianEnergy_nonneg R)

theorem hessianEnergy_smul (c : ℝ) (b : Corner.Vec) :
    hessianEnergy (c • b) = c^2 * hessianEnergy b := by
  rw [hessianEnergy_diagonal, hessianEnergy_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem inverseHessianVector_energy (R : Corner.Vec) :
    hessianEnergy (inverseHessianVector R) = dualHessianEnergy R := by
  rw [hessianEnergy_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  simp only [inverseHessianVector]
  field_simp [(hessian_diagonal_positive j).ne']

theorem inverseHessianVector_phase (R : Corner.Vec) :
    dotProduct (inverseHessianVector R) R = dualHessianEnergy R := by
  unfold dotProduct dualHessianEnergy inverseHessianVector
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dualHessianDistance_eq_norm (R : Corner.Vec) :
    dualHessianDistance R = ‖(WithLp.toLp 2 (inverseSqrtHessian.mulVec R) : Space)‖ := by
  have he : ‖(WithLp.toLp 2 (inverseSqrtHessian.mulVec R) : Space)‖^2 =
      dualHessianEnergy R := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    change ‖(inverseSqrtHessian.mulVec R) j‖^2 = (R j)^2 / hessian j j
    simp only [inverseSqrtHessian, Matrix.mulVec_diagonal,
      Real.norm_eq_abs, sq_abs, mul_pow, inv_pow,
      Real.sq_sqrt (hessian_diagonal_positive j).le, div_eq_mul_inv]
    ring
  rw [dualHessianDistance, ← he, Real.sqrt_sq (norm_nonneg _)]

theorem optimalTubeShift_energy (h : ℝ) (R : Corner.Vec) :
    hessianEnergy (optimalTubeShift h R) ≤ (99 / 100 : ℝ)^2 * h^2 := by
  rw [optimalTubeShift, hessianEnergy_smul, inverseHessianVector_energy,
    ← dualHessianDistance_sq R]
  by_cases hd : dualHessianDistance R = 0
  · rw [hd]
    norm_num
    positivity
  · have he : ((99 / 100 : ℝ) * h / dualHessianDistance R)^2 *
        dualHessianDistance R^2 = (99 / 100 : ℝ)^2 * h^2 := by
      field_simp
    exact he.le

theorem optimalTubeShift_phase (h : ℝ) (R : Corner.Vec) :
    dotProduct (optimalTubeShift h R) R = (99 / 100 : ℝ) * h * dualHessianDistance R := by
  rw [optimalTubeShift, smul_dotProduct, smul_eq_mul, inverseHessianVector_phase,
    ← dualHessianDistance_sq R]
  by_cases hd : dualHessianDistance R = 0
  · simp only [hd, div_zero, zero_mul, mul_zero]
  · field_simp

theorem euclidean_norm_sq_le_hessianEnergy (b : Corner.Vec) :
    ‖(WithLp.toLp 2 b : Space)‖^2 ≤ hessianEnergy b := by
  rw [EuclideanSpace.norm_sq_eq, hessianEnergy_diagonal]
  apply Finset.sum_le_sum
  intro j _
  change ‖b j‖^2 ≤ hessian j j * (b j)^2
  simpa only [Real.norm_eq_abs, sq_abs, one_mul] using
    mul_le_mul_of_nonneg_right (hessian_diagonal_ge_one j) (sq_nonneg (b j))

theorem optimalTubeShift_norm_le {h : ℝ} (h0 : 0 ≤ h) (R : Corner.Vec) :
    ‖(WithLp.toLp 2 (optimalTubeShift h R) : Space)‖ ≤ (99 / 100 : ℝ) * h := by
  have he := (euclidean_norm_sq_le_hessianEnergy (optimalTubeShift h R)).trans
    (optimalTubeShift_energy h R)
  nlinarith [norm_nonneg (WithLp.toLp 2 (optimalTubeShift h R) : Space)]

theorem optimalTubeShift_phase_nonneg {h : ℝ} (h0 : 0 ≤ h) (R : Corner.Vec) :
    0 ≤ dotProduct (optimalTubeShift h R) R := by
  rw [optimalTubeShift_phase]
  exact mul_nonneg (mul_nonneg (by norm_num) h0) (dualHessianDistance_nonneg R)

theorem tube_segment_energy {h : ℝ} (b : Corner.Vec)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    hessianEnergy (s • b) ≤ (99 / 100 : ℝ)^2 * h^2 := by
  rw [hessianEnergy_smul]
  have hs2 : s^2 ≤ 1 := by nlinarith [hs.1, hs.2]
  exact (mul_le_mul_of_nonneg_right hs2 (hessianEnergy_nonneg b)).trans
    (by simpa only [one_mul] using hb)

theorem optimalTubeShift_segment_phase {h s : ℝ} (h0 : 0 ≤ h) (hs : 0 ≤ s)
    (R : Corner.Vec) : 0 ≤ dotProduct (s • optimalTubeShift h R) R := by
  rw [smul_dotProduct, smul_eq_mul]
  exact mul_nonneg hs (optimalTubeShift_phase_nonneg h0 R)

theorem optimalTubeShift_cell_analytic {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q R : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    AnalyticAt ℂ (CellGauge.fullCellSymbol z σ)
      (shiftedMomentum q (s • optimalTubeShift h R)) :=
  CellGauge.fullCellSymbol_tube_analyticAt D hh hσ0 hσ q _ hq
    (tube_segment_energy _ (optimalTubeShift_energy h R) hs)

theorem optimalTubeShift_cell_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q R : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖CellGauge.fullCellSymbol z σ (shiftedMomentum q (s • optimalTubeShift h R))‖ ≤
      (2 : ℝ)^14 * (h^2)⁻¹ :=
  CellGauge.fullCellSymbol_tube_norm_le D hh hσ0 hσ q _ hq
    (tube_segment_energy _ (optimalTubeShift_energy h R) hs)

end Maxwell.Continuum.PeriodicBand
