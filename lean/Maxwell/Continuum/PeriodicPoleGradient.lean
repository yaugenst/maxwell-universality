import Maxwell.Continuum.PeriodicPoleDenominator
import Maxwell.Continuum.AnalyticBallTaylor
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! The exact first derivative of the actual rescaled denominator at its
imaginary pole. The transverse derivative vanishes by coordinate reflection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] dielectricBand imaginaryPole coordinateBand poleDenominator
  transverseBand poleSlope

theorem transverseBand_same (j : Fin 3) (c : ℂ) :
    transverseBand j j c = fun ζ => coordinateBand j (c + ζ) := by
  funext ζ
  unfold transverseBand coordinateBand
  rw [add_smul]

theorem poleDenominator_line {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j k : Fin 3) (ζ : ℂ) :
    poleDenominator D hh j (ζ • basisVector k) =
      ((h : ℂ) ^ 2)⁻¹ * (transverseBand j k
        ((imaginaryPole D hh j : ℂ) * Complex.I) ((h : ℂ) * ζ) - (z : ℂ)) := by
  unfold poleDenominator poleMomentum poleCenter transverseBand
  rw [smul_smul]

theorem poleDenominator_basis_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j k : Fin 3) :
    fderiv ℂ (poleDenominator D hh j) 0 (basisVector k) =
      (h : ℂ)⁻¹ * deriv (transverseBand j k
        ((imaginaryPole D hh j : ℂ) * Complex.I)) 0 := by
  have hc : ‖(imaginaryPole D hh j : ℂ) * Complex.I‖ < analyticRadius := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos (imaginaryPole_pos D hh j)]
    exact (imaginaryPole_mem_small D hh j).2.trans_lt
      ((imaginary_scale_bounds D.h_pos.le hh).1.trans_lt (by linarith only [analyticRadius_pos]))
  have ha := transverseBand_analyticAt j k (ζ := 0)
    (by simpa only [norm_zero, add_zero] using hc)
  have hm : HasDerivAt (fun ζ : ℂ => (h : ℂ) * ζ) (h : ℂ) 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℂ)).const_mul (h : ℂ)
  have hd := ha.differentiableAt.hasDerivAt.comp_of_eq (0 : ℂ) hm (by simp)
  have hres := (hd.sub_const (z : ℂ)).const_mul ((h : ℂ) ^ 2)⁻¹
  simp only [Function.comp_def] at hres
  have he : (fun ζ : ℂ => poleDenominator D hh j (ζ • basisVector k)) =
      fun ζ => ((h : ℂ) ^ 2)⁻¹ * (transverseBand j k
        ((imaginaryPole D hh j : ℂ) * Complex.I) ((h : ℂ) * ζ) - (z : ℂ)) :=
    funext (poleDenominator_line D hh j k)
  have hfirst := AnalyticBallBounds.line_first_coefficient
    (poleDenominator_analytic D hh j 0 (by simp)) (basisVector k)
  simp only [EvenTaylor.coefficient, Nat.factorial_one, Nat.cast_one,
    inv_one, one_mul, iteratedDeriv_one] at hfirst
  rw [← hfirst, he, hres.deriv]
  field_simp

theorem poleDenominator_basis_derivative_same {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j : Fin 3) :
    fderiv ℂ (poleDenominator D hh j) 0 (basisVector j) =
      (poleSlope D hh j : ℂ) * Complex.I := by
  rw [poleDenominator_basis_derivative, transverseBand_same,
    deriv_comp_const_add, add_zero]
  have hr := imaginaryPole_longitudinal_re D hh j
  have he : deriv (coordinateBand j) ((imaginaryPole D hh j : ℂ) * Complex.I) =
      (((deriv (coordinateBand j) ((imaginaryPole D hh j : ℂ) * Complex.I)).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa only [Complex.mul_I_re, Complex.ofReal_im, neg_zero] using hr
    · simp only [Complex.mul_I_im, Complex.ofReal_re]
  rw [he]
  unfold poleSlope
  push_cast
  ring

theorem poleDenominator_basis_derivative_other {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j k : Fin 3) (hjk : j ≠ k) :
    fderiv ℂ (poleDenominator D hh j) 0 (basisVector k) = 0 := by
  rw [poleDenominator_basis_derivative]
  unfold transverseBand
  rw [imaginaryPole_transverse_derivative D hh j k hjk, mul_zero]

theorem poleDenominator_fderiv_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j : Fin 3) (v : Momentum) :
    fderiv ℂ (poleDenominator D hh j) 0 v =
      ((poleSlope D hh j : ℂ) * Complex.I) * v j := by
  conv_lhs => rw [basis_expansion v]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [poleDenominator_basis_derivative_same]
    ring
  · intro k _ hkj
    rw [poleDenominator_basis_derivative_other D hh j k hkj.symm, mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Maxwell.Continuum.PeriodicBand
