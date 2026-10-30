import Maxwell.Continuum.CalibrationScaledFree
import Maxwell.Continuum.ClusterComplementLowBlock

/-! Arithmetic variation of the literal central 24-dimensional free
block. The central aliases have uniformly bounded directions. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open FreeFiber

theorem gridDirection_central (r : Fin 3 → ℝ) (hr : ∀ j, |r j| ≤ 1/16)
    (ν : Alias) (hν : IsCentralAlias ν) : directionSquare (gridDirection r ν) ≤ 1 := by
  have hc (j : Fin 3) : (gridDirection r ν j)^2 ≤ (81/256 : ℝ) := by
    have hrj := abs_le.mp (hr j)
    have hval : -(9/16 : ℝ) ≤ gridDirection r ν j ∧ gridDirection r ν j ≤ 9/16 := by
      rcases hν j with hj | hj <;> unfold gridDirection <;> rw [hj] <;> norm_num <;> constructor <;> linarith
    nlinarith [sq_nonneg (gridDirection r ν j-9/16), sq_nonneg (gridDirection r ν j+9/16)]
  unfold directionSquare
  calc
    _ ≤ ∑ _j : Fin 3, (81/256 : ℝ) := Finset.sum_le_sum (fun j _ => hc j)
    _ ≤ 1 := by norm_num

theorem block_real_scale (t E : ℝ) (a : Fin 3 → ℝ) :
    block (realMomentum (fun j => t*a j)) E =
      ((t^2 : ℝ) : ℂ) • block (realMomentum a) 0-(E : ℂ) • (1 : Polarization →L[ℂ] Polarization) := by
  have hsq : momentumSquare (realMomentum a) = (directionSquare a : ℂ) := by
    simp only [momentumSquare, directionSquare, realMomentum, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [block, blockMatrix, ClusterComplement.matrixCLM_sub, ClusterComplement.matrixCLM_smul,
    ClusterComplement.matrixCLM_one_eq, momentumSquare_scale_real, momentumOuter_scale_real]
  rw [block, blockMatrix, ClusterComplement.matrixCLM_sub, ClusterComplement.matrixCLM_smul,
    ClusterComplement.matrixCLM_one_eq, hsq]
  push_cast
  module

theorem block_real_scale_norm (t E : ℝ) (a : Fin 3 → ℝ)
    (ht : 0 ≤ t ∧ t ≤ 4) (hE : 0 ≤ E ∧ E ≤ 8) (ha : directionSquare a ≤ 1) :
    ‖block (realMomentum (fun j => t*a j)) E‖ ≤ 40 := by
  have hb : ‖block (realMomentum a) 0‖ ≤ 2 :=
    (ClusterComplement.block_zero_norm_le _).trans (by rw [← directionSquare_norm]; linarith)
  rw [block_real_scale]
  calc
    _ ≤ ‖((t^2 : ℝ) : ℂ) • block (realMomentum a) 0‖+‖(E : ℂ) • (1 : Polarization →L[ℂ] Polarization)‖ := norm_sub_le _ _
    _ ≤ t^2*2+E*1 := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
        abs_of_nonneg hE.1]
      exact add_le_add (mul_le_mul_of_nonneg_left hb (sq_nonneg t))
        (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hE.1)
    _ ≤ 40 := by nlinarith

theorem block_real_scale_rounding (t u E F : ℝ) (a : Fin 3 → ℝ)
    (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4) (ha : directionSquare a ≤ 1) :
    ‖block (realMomentum (fun j => t*a j)) E-block (realMomentum (fun j => u*a j)) F‖ ≤
      16*|t-u|+|E-F| := by
  have hb : ‖block (realMomentum a) 0‖ ≤ 2 :=
    (ClusterComplement.block_zero_norm_le _).trans (by rw [← directionSquare_norm]; linarith)
  rw [block_real_scale, block_real_scale]
  have heq : ((t^2 : ℝ) : ℂ) • block (realMomentum a) 0-(E : ℂ) • (1 : Polarization →L[ℂ] Polarization)-
      (((u^2 : ℝ) : ℂ) • block (realMomentum a) 0-(F : ℂ) • (1 : Polarization →L[ℂ] Polarization)) =
      (((t^2-u^2 : ℝ) : ℂ)) • block (realMomentum a) 0-
        (((E-F : ℝ) : ℂ)) • (1 : Polarization →L[ℂ] Polarization) := by push_cast; module
  rw [heq]
  calc
    _ ≤ ‖(((t^2-u^2 : ℝ) : ℂ)) • block (realMomentum a) 0‖+
      ‖(((E-F : ℝ) : ℂ)) • (1 : Polarization →L[ℂ] Polarization)‖ := norm_sub_le _ _
    _ ≤ |t^2-u^2| * 2+|E-F| := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := mul_le_mul_of_nonneg_left hb (abs_nonneg (t^2-u^2))
      have hn : ‖(1 : Polarization →L[ℂ] Polarization)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      have h2 := mul_le_mul_of_nonneg_left hn (abs_nonneg (E-F))
      linarith
    _ ≤ _ := by
      have he : t^2-u^2 = (t-u)*(t+u) := by ring
      rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ t+u)]
      have h := mul_le_mul_of_nonneg_left (show t+u ≤ 8 by linarith) (abs_nonneg (t-u))
      nlinarith

#print axioms block_real_scale_rounding

end Maxwell.Continuum.Calibration
