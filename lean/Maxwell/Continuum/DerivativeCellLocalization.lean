import Maxwell.Continuum.DerivativeCellKernel
import Maxwell.Continuum.FullCellSummable

/-! Literal off-cell decay and infinite-lattice summability for the
derivative resolvent. This is the one-cutoff operator in the weak
derivative identity, without regularity assumptions on cell restrictions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Auxiliary Bloch FreeFiber PeriodicBand OperatorFourier MasterConstants Set Metric Filter

theorem derivativeResolventSpatialBlock_stretched {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (a b : Bloch.Alias) :
    ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖ ≤
      (2 : ℝ)^88 * (h^4)⁻¹ *
        Real.exp (-Real.sqrt (800 * ‖integerVector (b-a)‖ / ((2 : ℝ)^257 / h)) / 64) := by
  have hb := cutoffDerivativeCellSymbol_fourier_decay D hh hσ0 hσ j (latticeShift b-latticeShift a)
  rw [latticeShift_sub_norm] at hb
  have he : 400 * (2 * ‖integerVector (b-a)‖) = 800 * ‖integerVector (b-a)‖ := by ring
  rw [he] at hb
  apply (derivativeResolventSpatialBlock_norm_le_kernel D hh hσ0 hσ j a b).trans
  apply (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 64)).trans
  have hc : (64 : ℝ) * (24 * 2^77) ≤ 2^88 := by norm_num
  calc
    _ = (64 * (24 * (2 : ℝ)^77)) * (h^4)⁻¹ *
        Real.exp (-Real.sqrt (800 * ‖integerVector (b-a)‖ / (2^257 / h)) / 64) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (by positivity)) (Real.exp_pos _).le

theorem derivativeResolventSpatialBlock_gevrey {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4 / 64)
    (j : Fin 3) (a b : Bloch.Alias) :
    ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖ ≤ Cs * L^4 *
      Real.exp (-cs * Real.sqrt (‖integerVector (b-a)‖ / L)) := by
  have hb := derivativeResolventSpatialBlock_stretched D (inverse_length_le_1024 hL) hσ0 hσ j a b
  simp only [inv_pow, inv_inv, div_inv_eq_mul] at hb
  have he : Real.exp (-Real.sqrt (800 * ‖integerVector (b-a)‖ / ((2 : ℝ)^257 * L)) / 64) ≤
      Real.exp (-cs * Real.sqrt (‖integerVector (b-a)‖ / L)) := by
    apply Real.exp_le_exp.mpr
    have hd := fullCell_decay_rate (length_pos hL) (norm_nonneg (integerVector (b-a)))
    linarith
  have hc : (2 : ℝ)^88 ≤ Cs := fixed_power_le_Cs (by have := exponent_large; omega)
  exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity))
    he (Real.exp_pos _).le (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4)))

theorem derivativeResolventSpatialBlock_polynomial {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (a b : Bloch.Alias) (K : ℕ) :
    ‖latticeShift b-latticeShift a‖^K * ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖ ≤
      ((2 : ℝ)^86 * (h^4)⁻¹) * ((2 : ℝ)^257/h)^K * (K.factorial : ℝ)^2 := by
  have hpos := D.h_pos
  have hK := angularFourier_gevrey_bound (cutoffDerivativeCellSymbol z σ j)
    (cutoffDerivativeCellSymbol_contDiff D hh hσ0 hσ j)
    (cutoffSymbol_compact (derivativeCellSymbol z σ j))
    ((cutoffSymbol_tsupport (derivativeCellSymbol z σ j)).trans
      (closedBall_subset_closedBall (by norm_num [smallRadius, backgroundAmplitude])))
    (by positivity : 0 ≤ (2 : ℝ)^77 * (h^4)⁻¹)
    (by positivity : 0 ≤ (2 : ℝ)^257/h)
    (fun k q v hv => cutoffDerivativeCellSymbol_gevrey D hh hσ0 hσ j q v hv k)
    (latticeShift b-latticeShift a) K
  calc
    _ ≤ ‖latticeShift b-latticeShift a‖^K *
        (64 * ‖angularFourier (cutoffDerivativeCellSymbol z σ j) (latticeShift b-latticeShift a)‖) :=
      mul_le_mul_of_nonneg_left (derivativeResolventSpatialBlock_norm_le_kernel D hh hσ0 hσ j a b)
        (by positivity)
    _ = 64 * (‖latticeShift b-latticeShift a‖^K *
        ‖angularFourier (cutoffDerivativeCellSymbol z σ j) (latticeShift b-latticeShift a)‖) := by ring
    _ ≤ 64 * (8 * ((2 : ℝ)^77 * (h^4)⁻¹) * ((2 : ℝ)^257/h)^K * (K.factorial : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hK (by norm_num)
    _ = _ := by ring

theorem derivativeResolventSpatialBlock_summable {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (a : Bloch.Alias) :
    Summable (fun b : Bloch.Alias => ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖) := by
  let C : ℝ := ((2 : ℝ)^86 * (h^4)⁻¹) * ((2 : ℝ)^257/h)^4 * ((4 : ℕ).factorial : ℝ)^2
  apply Summable.of_norm_bounded_eventually ((cellLattice_summable_inverse_four a).mul_left C)
  filter_upwards [eventually_cofinite_ne a] with b hne
  rw [norm_norm]
  have hp := integerVector_sub_norm_pos hne
  have hK := derivativeResolventSpatialBlock_polynomial D hh hσ0 hσ j a b 4
  rw [latticeShift_sub_norm] at hK
  have hk : ‖integerVector (b-a)‖^4 * ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖ ≤ C := by
    apply le_trans _ hK
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hp.le (by linarith) 4) (norm_nonneg _)
  calc
    _ ≤ C / ‖integerVector (b-a)‖^4 :=
      (le_div_iff₀ (pow_pos hp 4)).mpr (by simpa [mul_comm] using hk)
    _ = C * ‖integerVector (b-a)‖⁻¹^4 := by rw [div_eq_mul_inv, inv_pow]

theorem derivativeResolventSpatialBlock_sum_exists {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (a : Bloch.Alias) :
    Summable (fun b : Bloch.Alias => derivativeResolventSpatialBlock D hσ0 hσ j a b) :=
  (derivativeResolventSpatialBlock_summable D hh hσ0 hσ j a).of_norm

#print axioms derivativeResolventSpatialBlock_gevrey
#print axioms derivativeResolventSpatialBlock_polynomial
#print axioms derivativeResolventSpatialBlock_sum_exists

end Maxwell.Continuum.CellGauge
