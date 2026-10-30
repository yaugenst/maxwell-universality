import Maxwell.Continuum.FreeFiberNoncentral
import Mathlib.Tactic.Module

/-! Real free Maxwell blocks retain their exact longitudinal projector
when the common pi factor is approximated rationally. This gives
uniform arithmetic control without cutting off high aliases. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open FreeFiber

def directionSquare (a : Fin 3 → ℝ) : ℝ := ∑ j, a j^2

theorem directionSquare_norm (a : Fin 3 → ℝ) :
    directionSquare a = ‖momentumVector (realMomentum a)‖^2 := by
  simp only [directionSquare, EuclideanSpace.norm_sq_eq, momentumVector, realMomentum,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

def longitudinal (a : Fin 3 → ℝ) : Polarization →L[ℂ] Polarization :=
  ((directionSquare a : ℂ))⁻¹ • matrixCLM (momentumOuter (realMomentum a))

theorem longitudinal_norm (a : Fin 3 → ℝ) (ha : 0 < directionSquare a) : ‖longitudinal a‖ = 1 := by
  rw [longitudinal, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha, momentumOuter_norm, ← directionSquare_norm, inv_mul_cancel₀ ha.ne']

theorem transverse_norm (a : Fin 3 → ℝ) (ha : 0 < directionSquare a) :
    ‖(1 : Polarization →L[ℂ] Polarization)-longitudinal a‖ ≤ 2 := by
  calc
    _ ≤ ‖(1 : Polarization →L[ℂ] Polarization)‖+‖longitudinal a‖ := norm_sub_le _ _
    _ ≤ 1+1 := add_le_add ContinuousLinearMap.norm_id_le (longitudinal_norm a ha).le
    _ = _ := by norm_num

theorem momentumSquare_scale_real (t : ℝ) (a : Fin 3 → ℝ) :
    momentumSquare (realMomentum (fun j => t*a j)) = ((t^2*directionSquare a : ℝ) : ℂ) := by
  simp only [momentumSquare, realMomentum, Complex.ofReal_mul, mul_pow,
    ← Finset.mul_sum, directionSquare, Complex.ofReal_sum, Complex.ofReal_pow]

theorem momentumOuter_scale_real (t : ℝ) (a : Fin 3 → ℝ) :
    matrixCLM (momentumOuter (realMomentum (fun j => t*a j))) =
      ((t : ℂ)^2) • matrixCLM (momentumOuter (realMomentum a)) := by
  have hm : momentumOuter (realMomentum (fun j => t*a j)) =
      ((t : ℂ)^2) • momentumOuter (realMomentum a) := by
    ext i j
    simp only [momentumOuter, realMomentum, Matrix.vecMulVec_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  rw [hm]
  simp only [matrixCLM, map_smul]

theorem inverseBlock_longitudinal (t E : ℝ) (a : Fin 3 → ℝ)
    (ha : directionSquare a ≠ 0) (hE : E ≠ 0) (hd : t^2*directionSquare a-E ≠ 0) :
    inverseBlock (realMomentum (fun j => t*a j)) E =
      (-((E : ℂ))⁻¹) • longitudinal a+
        (((t^2*directionSquare a-E : ℝ) : ℂ))⁻¹ •
          ((1 : Polarization →L[ℂ] Polarization)-longitudinal a) := by
  rw [inverseBlock_eq_CLM, momentumSquare_scale_real, momentumOuter_scale_real]
  simp only [Complex.ofReal_sub]
  have haC : (directionSquare a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hEC : (E : ℂ) ≠ 0 := by exact_mod_cast hE
  have hdC : (t : ℂ)^2*(directionSquare a : ℂ)-(E : ℂ) ≠ 0 := by
    exact_mod_cast hd
  have hc : -((t : ℂ)^2*(directionSquare a : ℂ)-(E : ℂ))⁻¹*(E : ℂ)⁻¹*(t : ℂ)^2 =
      (-(E : ℂ)⁻¹-((t : ℂ)^2*(directionSquare a : ℂ)-(E : ℂ))⁻¹)*
        (directionSquare a : ℂ)⁻¹ := by
    field_simp
    ring
  unfold longitudinal
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  linear_combination (norm := module) hc • matrixCLM (momentumOuter (realMomentum a))

#print axioms inverseBlock_longitudinal

end Maxwell.Continuum.Calibration
