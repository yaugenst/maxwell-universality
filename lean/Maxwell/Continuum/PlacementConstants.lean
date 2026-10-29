import Maxwell.Continuum.PeriodicHessianError

/-! Exact rational certification of the fixed integer placement lattice.
The margins include the complete stated continuum Hessian error. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber

def placementDiagonal : Fin 3 → ℤ :=
  ![7180532256056349, 6388184103869743, 2347449745487106]

def placementMatrix : Matrix (Fin 3) (Fin 3) ℤ := Matrix.diagonal placementDiagonal

private def coefficientLower : Fin 3 → ℝ :=
  ![47 / 31 + 352 * (435 / 100) / 589,
    2 + 11 * (435 / 100) / 38, 1 / 8 + 11 * (435 / 100) / 152]

private def coefficientUpper : Fin 3 → ℝ :=
  ![47 / 31 + 352 * (436 / 100) / 589,
    2 + 11 * (436 / 100) / 38, 1 / 8 + 11 * (436 / 100) / 152]

def cornerEntryLower : Fin 3 → ℝ := ![4058 / 100, 3213 / 100, 433 / 100]

def cornerEntryUpper : Fin 3 → ℝ := ![4090 / 100, 3237 / 100, 438 / 100]

theorem cornerEntry_enclosure (j : Fin 3) :
    cornerEntryLower j ≤ Real.pi ^ 2 * Corner.hessianCoefficient j ∧
      Real.pi ^ 2 * Corner.hessianCoefficient j ≤ cornerEntryUpper j := by
  have hs : (435 / 100 : ℝ) ≤ Real.sqrt 19 ∧ Real.sqrt 19 ≤ (436 / 100 : ℝ) := by
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)
    have hn := Real.sqrt_nonneg (19 : ℝ)
    constructor <;> nlinarith
  have hc : coefficientLower j ≤ Corner.hessianCoefficient j ∧
      Corner.hessianCoefficient j ≤ coefficientUpper j := by
    fin_cases j <;>
      norm_num [coefficientLower, coefficientUpper, Corner.hessianCoefficient] <;>
      constructor <;> nlinarith [hs.1, hs.2]
  have hc0 : 0 ≤ coefficientLower j := by fin_cases j <;> norm_num [coefficientLower]
  have hc1 : 0 ≤ Corner.hessianCoefficient j := hc0.trans hc.1
  have hp : (314 / 100 : ℝ)^2 ≤ Real.pi^2 ∧ Real.pi^2 ≤ (315 / 100 : ℝ)^2 := by
    constructor <;> nlinarith [Real.pi_gt_d2, Real.pi_lt_d2, Real.pi_pos]
  have hlo := mul_le_mul hp.1 hc.1 hc0 (sq_nonneg Real.pi)
  have hhi := mul_le_mul hp.2 hc.2 hc1 (by norm_num : (0 : ℝ) ≤ (315 / 100)^2)
  fin_cases j <;>
    norm_num [coefficientLower, coefficientUpper, cornerEntryLower, cornerEntryUpper,
      Corner.hessianCoefficient] at * <;> constructor <;> linarith

theorem placement_squared_allowance (j : Fin 3) :
    (99 / 100 : ℝ)^2 * (Real.pi^2 * Corner.hessianCoefficient j + ((2 : ℝ)^60)⁻¹) ≤
        backgroundAmplitude * (placementDiagonal j : ℝ)^2 ∧
      backgroundAmplitude * (placementDiagonal j : ℝ)^2 ≤
        (101 / 100 : ℝ)^2 * (Real.pi^2 * Corner.hessianCoefficient j - ((2 : ℝ)^60)⁻¹) := by
  have hc := cornerEntry_enclosure j
  have hlo : (99 / 100 : ℝ)^2 * (cornerEntryUpper j + ((2 : ℝ)^60)⁻¹) ≤
      backgroundAmplitude * (placementDiagonal j : ℝ)^2 := by
    fin_cases j <;> norm_num [cornerEntryUpper, backgroundAmplitude, placementDiagonal]
  have hhi : backgroundAmplitude * (placementDiagonal j : ℝ)^2 ≤
      (101 / 100 : ℝ)^2 * (cornerEntryLower j - ((2 : ℝ)^60)⁻¹) := by
    fin_cases j <;> norm_num [cornerEntryLower, backgroundAmplitude, placementDiagonal]
  constructor <;> nlinarith [hc.1, hc.2]

theorem placement_diagonal_squared (j : Fin 3) :
    (99 / 100 : ℝ)^2 * hessian j j ≤ (placementDiagonal j : ℝ)^2 ∧
      (placementDiagonal j : ℝ)^2 ≤ (101 / 100 : ℝ)^2 * hessian j j := by
  obtain ⟨heLo, heHi⟩ := abs_le.mp (hessian_diagonal_error j)
  obtain ⟨hbLo, hbHi⟩ := placement_squared_allowance j
  have hρ := backgroundAmplitude_pos
  constructor
  · apply (mul_le_mul_iff_right₀ hρ).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hρ).mp
    nlinarith

theorem hessian_diagonal_positive (j : Fin 3) : 0 < hessian j j := by
  have h := (hessian_bounds (Pi.single j 1)).1
  have hρ := backgroundAmplitude_pos
  have hd : dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1) = 1 := by
    simp [dotProduct, Pi.single_apply]
  have hq : dotProduct (Pi.single j (1 : ℝ)) (hessian.mulVec (Pi.single j 1)) =
      hessian j j := by simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [hd, hq, mul_one] at h
  exact lt_of_lt_of_le (by positivity) h

end Maxwell.Continuum.PeriodicBand
