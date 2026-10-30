import Maxwell.Continuum.FullCellGevrey
import Maxwell.Continuum.FullCellKernel
import Maxwell.Continuum.MasterConstants

/-! Stretched-exponential and arbitrary polynomial decay between literal
physical period cells. No cell trace or restriction regularity is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Auxiliary Bloch FreeFiber PeriodicBand OperatorFourier MasterConstants Set Metric

theorem latticeShift_sub_norm (a b : Bloch.Alias) :
    ‖latticeShift b - latticeShift a‖ = 2 * ‖integerVector (b-a)‖ := by
  have he : latticeShift b - latticeShift a = (2 : ℝ) • integerVector (b-a) := by
    apply PiLp.ext
    intro j
    simp only [latticeShift, PiLp.sub_apply, PiLp.smul_apply, integerVector_apply,
      Pi.sub_apply, Int.cast_sub, smul_eq_mul]
    ring
  rw [he, norm_smul, Real.norm_ofNat]

theorem resolventSpatialBlock_stretched {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (a b : Bloch.Alias) :
    ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤
      (2 : ℝ)^70 * (h^2)⁻¹ *
        Real.exp (-Real.sqrt (800 * ‖integerVector (b-a)‖ / ((2 : ℝ)^257 / h)) / 64) := by
  have hb := cutoffFullCellSymbol_fourier_decay D hh hσ0 hσ (latticeShift b-latticeShift a)
  rw [latticeShift_sub_norm] at hb
  have he : 400 * (2 * ‖integerVector (b-a)‖) = 800 * ‖integerVector (b-a)‖ := by ring
  rw [he] at hb
  apply (resolventSpatialBlock_norm_le_kernel D hσ0 hσ a b).trans
  apply (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 64)).trans
  have hc : (64 : ℝ) * (24 * 2^59) ≤ 2^70 := by norm_num
  calc
    _ = (64 * (24 * (2 : ℝ)^59)) * (h^2)⁻¹ *
        Real.exp (-Real.sqrt (800 * ‖integerVector (b-a)‖ / (2^257 / h)) / 64) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr (sq_nonneg h))) (Real.exp_pos _).le

theorem fullCell_decay_rate {L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) :
    cs * Real.sqrt (r/L) ≤ Real.sqrt (800*r / ((2 : ℝ)^257 * L)) / 64 := by
  have hc : (64 * cs)^2 ≤ 800 / (2 : ℝ)^257 := by norm_num [cs]
  have hs := Real.sq_sqrt (div_nonneg hr hL.le)
  have ht := Real.sq_sqrt (show 0 ≤ 800*r / ((2 : ℝ)^257 * L) by positivity)
  have hm := mul_le_mul_of_nonneg_right hc (div_nonneg hr hL.le)
  have he : (800 / (2 : ℝ)^257) * (r/L) = 800*r / ((2 : ℝ)^257 * L) := by ring
  rw [he] at hm
  have hcs := cs_pos
  have hn := Real.sqrt_nonneg (r/L)
  have hn' := Real.sqrt_nonneg (800*r / ((2 : ℝ)^257 * L))
  nlinarith [sq_nonneg (64*cs*Real.sqrt (r/L) -
    Real.sqrt (800*r / ((2 : ℝ)^257 * L)))]

/-- The paper's summable cell bound for the literal complete cutoff inverse. -/
theorem resolventSpatialBlock_gevrey {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4 / 64)
    (a b : Bloch.Alias) :
    ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤ Cs * L^4 *
      Real.exp (-cs * Real.sqrt (‖integerVector (b-a)‖ / L)) := by
  have hb := resolventSpatialBlock_stretched D (inverse_length_le_1024 hL) hσ0 hσ a b
  simp only [inv_pow, inv_inv, div_inv_eq_mul] at hb
  have he : Real.exp (-Real.sqrt (800 * ‖integerVector (b-a)‖ / ((2 : ℝ)^257 * L)) / 64) ≤
      Real.exp (-cs * Real.sqrt (‖integerVector (b-a)‖ / L)) := by
    apply Real.exp_le_exp.mpr
    have hd := fullCell_decay_rate (length_pos hL) (norm_nonneg (integerVector (b-a)))
    linarith
  have hL1 := length_ge_one hL
  have h2 : L^2 ≤ L^4 := by nlinarith [sq_nonneg (L^2-1)]
  have hc : (2 : ℝ)^70 ≤ Cs := fixed_power_le_Cs (by have := exponent_large; omega)
  exact hb.trans (mul_le_mul (mul_le_mul hc h2 (sq_nonneg L) Cs_pos.le)
    he (Real.exp_pos _).le (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4)))

theorem resolventSpatialBlock_polynomial {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (a b : Bloch.Alias) (K : ℕ) :
    ‖latticeShift b-latticeShift a‖^K * ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤
      ((2 : ℝ)^68 * (h^2)⁻¹) * ((2 : ℝ)^257/h)^K * (K.factorial : ℝ)^2 := by
  have hpos := D.h_pos
  have hK := angularFourier_gevrey_bound (cutoffFullCellSymbol z σ)
    (cutoffFullCellSymbol_contDiff D hh hσ0 hσ) (cutoffSymbol_compact (fullCellSymbol z σ))
    ((cutoffSymbol_tsupport (fullCellSymbol z σ)).trans
      (closedBall_subset_closedBall (by norm_num [smallRadius, backgroundAmplitude])))
    (by positivity : 0 ≤ (2 : ℝ)^59 * (h^2)⁻¹)
    (by positivity : 0 ≤ (2 : ℝ)^257/h)
    (fun k q v hv => cutoffFullCellSymbol_gevrey D hh hσ0 hσ q v hv k)
    (latticeShift b-latticeShift a) K
  calc
    _ ≤ ‖latticeShift b-latticeShift a‖^K *
        (64 * ‖angularFourier (cutoffFullCellSymbol z σ) (latticeShift b-latticeShift a)‖) :=
      mul_le_mul_of_nonneg_left (resolventSpatialBlock_norm_le_kernel D hσ0 hσ a b) (by positivity)
    _ = 64 * (‖latticeShift b-latticeShift a‖^K *
        ‖angularFourier (cutoffFullCellSymbol z σ) (latticeShift b-latticeShift a)‖) := by ring
    _ ≤ 64 * (8 * ((2 : ℝ)^59 * (h^2)⁻¹) * ((2 : ℝ)^257/h)^K * (K.factorial : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hK (by norm_num)
    _ = _ := by ring

#print axioms resolventSpatialBlock_gevrey
#print axioms resolventSpatialBlock_polynomial

end Maxwell.Continuum.CellGauge
