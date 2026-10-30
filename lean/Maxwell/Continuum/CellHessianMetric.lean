import Maxwell.Continuum.CellSpatialCover
import Maxwell.Continuum.PeriodicTubeShift
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The exact continuum Hessian metric controls displacement errors
inside a pair of finite broad-well cell covers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open PeriodicBand Bloch

def hessianCoordinates : Space →L[ℝ] Space :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) inverseSqrtHessian

theorem hessianCoordinates_norm (R : Space) :
    ‖hessianCoordinates R‖ = dualHessianDistance R.ofLp :=
  (dualHessianDistance_eq_norm R.ofLp).symm

theorem dualHessianDistance_le_norm (R : Space) : dualHessianDistance R.ofLp ≤ ‖R‖ := by
  have he : dualHessianEnergy R.ofLp ≤ ‖R‖^2 := by
    rw [dualHessianEnergy, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change (R j)^2 / hessian j j ≤ ‖R j‖^2
    rw [Real.norm_eq_abs, sq_abs]
    exact div_le_self (sq_nonneg _) (hessian_diagonal_ge_one j)
  have hs := dualHessianDistance_sq R.ofLp
  nlinarith [dualHessianDistance_nonneg R.ofLp, norm_nonneg R]

theorem dualHessianDistance_neg (R : Space) :
    dualHessianDistance (-R).ofLp = dualHessianDistance R.ofLp := by
  rw [← hessianCoordinates_norm, map_neg, norm_neg, hessianCoordinates_norm]

theorem dualHessianDistance_triangle (R S : Space) :
    dualHessianDistance R.ofLp ≤ dualHessianDistance S.ofLp + ‖R-S‖ := by
  rw [← hessianCoordinates_norm, ← hessianCoordinates_norm]
  have he : hessianCoordinates R = hessianCoordinates S + hessianCoordinates (R-S) := by
    rw [map_sub]
    abel
  rw [he]
  have hc : ‖hessianCoordinates (R-S)‖ ≤ ‖R-S‖ := by
    rw [hessianCoordinates_norm]
    exact dualHessianDistance_le_norm (R-S)
  exact (norm_add_le _ _).trans (add_le_add le_rfl hc)

theorem wellCells_dualDistance_lower {L : ℝ} (hL : 1 ≤ L) (k : Bloch.Alias)
    {a b : Bloch.Alias} (ha : a ∈ ballCells L) (hb : b ∈ wellCells L k) :
    dualHessianDistance (latticeShift k).ofLp ≤
      dualHessianDistance (latticeShift a-latticeShift b).ofLp + 48*L := by
  have he : -latticeShift k - (latticeShift a-latticeShift b) =
      (latticeShift b-latticeShift k) - latticeShift a := by abel
  have hn : ‖-latticeShift k - (latticeShift a-latticeShift b)‖ ≤ 48*L := by
    rw [he]
    exact (norm_sub_le _ _).trans
      (by linarith [wellCells_center_norm_le hL k hb, ballCells_shift_norm_le hL ha])
  have ht := dualHessianDistance_triangle (-latticeShift k) (latticeShift a-latticeShift b)
  rw [dualHessianDistance_neg] at ht
  linarith

theorem exp_fortyEight_le : Real.exp (48 : ℝ) ≤ (2 : ℝ)^96 := by
  have he : Real.exp (48 : ℝ) = (Real.exp 1)^48 := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 48
  rw [he, show (2 : ℝ)^96 = (4 : ℝ)^48 by norm_num]
  exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_three]) 48

theorem wellCells_exponential_le {L : ℝ} (hL : 1 ≤ L) (k : Bloch.Alias)
    {a b : Bloch.Alias} (ha : a ∈ ballCells L) (hb : b ∈ wellCells L k) :
    Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift a-latticeShift b).ofLp) ≤
      (2 : ℝ)^96 * Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift k).ofLp) := by
  have hLp : 0 < L := by linarith
  have hl := mul_le_mul_of_nonneg_left (wellCells_dualDistance_lower hL k ha hb)
    (show 0 ≤ (99/100 : ℝ)*L⁻¹ by positivity)
  have he : (99/100 : ℝ)*L⁻¹*(48*L) = (99/100 : ℝ)*48 := by
    field_simp
  have harg : -(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift a-latticeShift b).ofLp ≤
      48 + (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift k).ofLp) := by
    rw [mul_add, he] at hl
    linarith
  calc
    _ ≤ Real.exp (48 + (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift k).ofLp)) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp 48 * Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift k).ofLp) :=
      Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right exp_fortyEight_le (Real.exp_pos _).le

#print axioms wellCells_dualDistance_lower
#print axioms wellCells_exponential_le

end Maxwell.Continuum.CellGauge
