import Maxwell.Continuum.PeriodicPoleLocalFourier
import Maxwell.Continuum.PeriodicSeparatedFourier

/-! The local pole and both actual global remainders in one scalar
Fourier asymptotic, with the physical sign convention and placement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary EffectiveMass MeasureTheory

attribute [local irreducible] realMode

def fullSourceSymbol {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (k : Space) : ℂ :=
  cutoffSelectedQuotient D hh j k+separatedRegularSymbol D hh j (realMode D hh) (realMode D hh) k

theorem fullSourceSymbol_fourier_split {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (R : Space) :
    OperatorFourier.angularFourier (fullSourceSymbol D hh j) R =
      OperatorFourier.angularFourier (localSelectedSymbol D hh j) R+
        OperatorFourier.angularFourier (regularSelectedSymbol D hh j) R+
        OperatorFourier.angularFourier (separatedRegularSymbol D hh j (realMode D hh) (realMode D hh)) R := by
  have he : OperatorFourier.angularFourier (fullSourceSymbol D hh j) R =
      OperatorFourier.angularFourier (cutoffSelectedQuotient D hh j) R+
        OperatorFourier.angularFourier (separatedRegularSymbol D hh j (realMode D hh) (realMode D hh)) R := by
    simp only [OperatorFourier.angularFourier_integral, fullSourceSymbol, smul_eq_mul, mul_add]
    apply integral_add
    · simpa only [smul_eq_mul] using OperatorFourier.angularPhase_integrable
        (cutoffSelectedQuotient_integrable D hh j) R
    · simpa only [smul_eq_mul] using OperatorFourier.angularPhase_integrable
        (separatedRegularSymbol_integrable D hh j (realMode D hh) (realMode D hh)) R
  rw [he, selectedSymbol_fourier_split]

theorem fullSourceSymbol_fourier_remainder {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖OperatorFourier.angularFourier (fullSourceSymbol D hh j) (-T • PiLp.single 2 j 1)-
      OperatorFourier.angularFourier (localSelectedSymbol D hh j) (-T • PiLp.single 2 j 1)‖ ≤
      2*((2 : ℝ)^220000*h⁻¹/T^16) := by
  have hr : ‖OperatorFourier.angularFourier (regularSelectedSymbol D hh j) (-T • PiLp.single 2 j 1)‖ ≤
      (2 : ℝ)^220000*h⁻¹/T^16 := by
    apply (le_div_iff₀ (pow_pos hT 16)).mpr
    simpa only [abs_neg, abs_of_pos hT, mul_comm] using regularSelectedSymbol_fourier_weighted D hh j (-T)
  have hs : ‖OperatorFourier.angularFourier
      (separatedRegularSymbol D hh j (realMode D hh) (realMode D hh)) (-T • PiLp.single 2 j 1)‖ ≤
      (2 : ℝ)^220000*h⁻¹/T^16 := by
    apply (le_div_iff₀ (pow_pos hT 16)).mpr
    simpa only [abs_neg, abs_of_pos hT, mul_comm] using separatedRegularSymbol_fourier_weighted
      D hh j (realMode_norm D hh).le (realMode_norm D hh).le (-T)
  rw [fullSourceSymbol_fourier_split]
  have he (a b c : ℂ) : a+b+c-a = b+c := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hr hs).trans_eq (two_mul _).symm)

theorem fullSourceSymbol_fourier_placement {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {d : ℝ} (hd : 1 ≤ d) :
    ‖(Real.exp (-poleAction D hh j*d) : ℂ)*
      OperatorFourier.angularFourier (fullSourceSymbol D hh j)
        (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1)-
      (Real.exp (-poleAction D hh j*d) : ℂ)*((selectedLeadingCoefficient D hh j/d : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^70069*Real.exp (-poleAction D hh j*d)/(d*Real.sqrt d)+
        2*((2 : ℝ)^220000*h⁻¹*Real.exp (-poleAction D hh j*d)/d^16) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hh0 := D.h_pos
  let T : ℝ := 2*(placementDiagonal j : ℝ)*d
  have hTd : d ≤ T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (placementDiagonal_residue_bounds j).1 hd0.le
  have hT : 0 < T := hd0.trans_le hTd
  have hr := fullSourceSymbol_fourier_remainder D hh j hT
  have hp : 2*((2 : ℝ)^220000*h⁻¹/T^16) ≤ 2*((2 : ℝ)^220000*h⁻¹/d^16) := by
    gcongr
  have hb : ‖(Real.exp (-poleAction D hh j*d) : ℂ)*
      OperatorFourier.angularFourier (fullSourceSymbol D hh j) (-T • PiLp.single 2 j 1)-
      (Real.exp (-poleAction D hh j*d) : ℂ)*
      OperatorFourier.angularFourier (localSelectedSymbol D hh j) (-T • PiLp.single 2 j 1)‖ ≤
        2*((2 : ℝ)^220000*h⁻¹*Real.exp (-poleAction D hh j*d)/d^16) := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he (a b c e : ℝ) : a*(2*(b*c/e)) = 2*(b*c*a/e) := by ring
    exact (mul_le_mul_of_nonneg_left (hr.trans hp) (Real.exp_pos _).le).trans_eq (he _ _ _ _)
  apply (norm_sub_le_norm_sub_add_norm_sub _
    ((Real.exp (-poleAction D hh j*d) : ℂ)*
      OperatorFourier.angularFourier (localSelectedSymbol D hh j) (-T • PiLp.single 2 j 1)) _).trans
  exact (add_le_add hb (localSelectedSymbol_fourier_placement D hh j hd)).trans_eq (add_comm _ _)

#print axioms fullSourceSymbol_fourier_placement

end Maxwell.Continuum.PeriodicBand
