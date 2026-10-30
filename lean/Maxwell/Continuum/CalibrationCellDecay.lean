import Maxwell.Continuum.FullCellLocalization

/-! Decay of the actual common-coordinate cell maps. These are the maps
whose periodic images can be summed in a single operator Banach space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Auxiliary Bloch FreeFiber PeriodicBand OperatorFourier MasterConstants CellBandFourier

theorem resolventCellBlock_norm_le_kernel {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (a b : Bloch.Alias) :
    ‖resolventCellBlock D hσ0 hσ a b‖ ≤
      64*‖angularFourier (cutoffFullCellSymbol z σ) (latticeShift b-latticeShift a)‖ := by
  rw [resolventCellBlock_eq, norm_smul, norm_mul, carrier_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) blochDensity_pos)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [blochDensity_le_one]

theorem resolventCellBlock_stretched {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (a b : Bloch.Alias) :
    ‖resolventCellBlock D hσ0 hσ a b‖ ≤ (2 : ℝ)^70*(h^2)⁻¹*
      Real.exp (-Real.sqrt (800*‖integerVector (b-a)‖/((2 : ℝ)^257/h))/64) := by
  have hb := cutoffFullCellSymbol_fourier_decay D hh hσ0 hσ (latticeShift b-latticeShift a)
  rw [latticeShift_sub_norm] at hb
  rw [show 400*(2*‖integerVector (b-a)‖) = 800*‖integerVector (b-a)‖ by ring] at hb
  apply (resolventCellBlock_norm_le_kernel D hσ0 hσ a b).trans
  apply (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 64)).trans
  have hc : (64 : ℝ)*(24*2^59) ≤ 2^70 := by norm_num
  calc
    _ = (64*(24*(2 : ℝ)^59))*(h^2)⁻¹*
        Real.exp (-Real.sqrt (800*‖integerVector (b-a)‖/(2^257/h))/64) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr (sq_nonneg h))) (Real.exp_pos _).le

theorem resolventCellBlock_gevrey {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (a b : Bloch.Alias) :
    ‖resolventCellBlock D hσ0 hσ a b‖ ≤ Cs*L^4*
      Real.exp (-cs*Real.sqrt (‖integerVector (b-a)‖/L)) := by
  have hb := resolventCellBlock_stretched D (inverse_length_le_1024 hL) hσ0 hσ a b
  simp only [inv_pow, inv_inv, div_inv_eq_mul] at hb
  have he : Real.exp (-Real.sqrt (800*‖integerVector (b-a)‖/((2 : ℝ)^257*L))/64) ≤
      Real.exp (-cs*Real.sqrt (‖integerVector (b-a)‖/L)) := by
    apply Real.exp_le_exp.mpr
    have hd := fullCell_decay_rate (length_pos hL) (norm_nonneg (integerVector (b-a)))
    linarith
  have hL1 := length_ge_one hL
  have h2 : L^2 ≤ L^4 := by nlinarith [sq_nonneg (L^2-1)]
  have hc : (2 : ℝ)^70 ≤ Cs := fixed_power_le_Cs (by have := exponent_large; omega)
  exact hb.trans (mul_le_mul (mul_le_mul hc h2 (sq_nonneg L) Cs_pos.le) he
    (Real.exp_pos _).le (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4)))

#print axioms resolventCellBlock_gevrey

end Maxwell.Continuum.CellGauge
