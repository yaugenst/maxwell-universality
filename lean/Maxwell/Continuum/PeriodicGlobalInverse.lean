import Maxwell.Continuum.PeriodicGlobalDenominator
import Maxwell.Continuum.AnalyticSymbolInverse
import Maxwell.Continuum.PoleChartCutoff
import Maxwell.Continuum.MasterConstantLedger

/-! Actual reciprocal-symbol estimates outside the fixed pole core.
The zero-free disk is constructed from the proved denominator bounds;
no inverse or derivative estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 16384

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] poleDenominator dielectricBand imaginaryPole

def globalPoleCoercivity : ℝ := (2^8210 : ℝ)⁻¹

theorem globalPole_constants : 0 < globalPoleCoercivity ∧
    globalPoleCoercivity ≤ 2*(2 : ℝ)^116 ∧
    8*globalPoleCoercivity ≤ poleCoreRadius^2 ∧
    2/globalPoleCoercivity = (2 : ℝ)^8211 ∧
    globalPoleCoercivity/(2*(2 : ℝ)^116) = (2^8327 : ℝ)⁻¹ := by
  norm_num [globalPoleCoercivity, poleCoreRadius]

theorem globalPole_outside_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖) :
    globalPoleCoercivity*(globalPoleRadius k)^2 ≤
      ‖poleDenominator D hh j (realMomentum k.ofLp)‖ := by
  have hr : poleCoreRadius ≤ 1 := by norm_num [poleCoreRadius]
  have hn : poleCoreRadius*‖k‖ ≤ ‖k‖ :=
    (mul_le_mul_of_nonneg_right hr (norm_nonneg k)).trans_eq (one_mul _)
  have hl : poleCoreRadius*globalPoleRadius k ≤ 2*‖k‖ := by
    unfold globalPoleRadius
    nlinarith only [hk0, hn]
  have hs := pow_le_pow_left₀
    (mul_nonneg poleCutoff_scales.2.2.1.le (globalPoleRadius_pos k).le) hl 2
  have hc := mul_le_mul_of_nonneg_right globalPole_constants.2.2.1
    (sq_nonneg (globalPoleRadius k))
  apply le_trans _ (globalPole_denominator_norm_lower D hh j k hk)
  nlinarith only [hs, hc]

theorem globalPole_inverse_line_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖)
    {v : Momentum} (hv : ‖v‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun ζ : ℂ =>
      (poleDenominator D hh j (realMomentum k.ofLp + ζ • v))⁻¹)
      (closedBall 0 ((2^8327 : ℝ)⁻¹*globalPoleRadius k)) := by
  rw [← globalPole_constants.2.2.2.2]
  apply AnalyticSymbolInverse.reciprocal_analytic (globalPoleRadius_pos k)
    (by positivity) globalPole_constants.1 globalPole_constants.2.1
    (globalPole_line_analytic D hh j k hk hv)
    (fun ζ hζ => globalPole_line_norm_le D hh j k hk hv
      (by simpa only [mem_closedBall, dist_zero_right] using hζ))
  simpa only [zero_smul, add_zero] using globalPole_outside_lower D hh j k hk hk0

theorem globalPole_inverse_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖)
    {v : Momentum} (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n (fun ζ : ℂ =>
      (poleDenominator D hh j (realMomentum k.ofLp + ζ • v))⁻¹) 0‖ ≤
      (n.factorial : ℝ)*(2 : ℝ)^(8211+8327*n)/(globalPoleRadius k)^2 := by
  have he := AnalyticSymbolInverse.reciprocal_iteratedDeriv (globalPoleRadius_pos k)
    (by positivity : (0 : ℝ) < 2^116) globalPole_constants.1 globalPole_constants.2.1
    (globalPole_line_analytic D hh j k hk hv)
    (fun ζ hζ => globalPole_line_norm_le D hh j k hk hv
      (by simpa only [mem_closedBall, dist_zero_right] using hζ))
    (by simpa only [zero_smul, add_zero] using globalPole_outside_lower D hh j k hk hk0) n
  have hquot : 2/(globalPoleCoercivity*(globalPoleRadius k)^2) =
      (2 : ℝ)^8211/(globalPoleRadius k)^2 := by
    rw [← globalPole_constants.2.2.2.1]
    ring
  rw [globalPole_constants.2.2.2.2, hquot] at he
  apply he.trans
  have hbase : (2^8327 : ℝ)⁻¹ ≤ (2^8327 : ℝ)⁻¹*globalPoleRadius k := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (globalPoleRadius_ge_one k)
      (by positivity : 0 ≤ (2^8327 : ℝ)⁻¹)
  calc
    _ ≤ (n.factorial : ℝ)*((2 : ℝ)^8211/(globalPoleRadius k)^2) /
        ((2^8327 : ℝ)⁻¹)^n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hbase n)
    _ = _ := by
      rw [inv_pow, div_inv_eq_mul, ← pow_mul, pow_add]
      ring

theorem globalPole_inverse_derivative_sixteen {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖)
    {v : Momentum} (hv : ‖v‖ ≤ 1) {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun ζ : ℂ =>
      (poleDenominator D hh j (realMomentum k.ofLp + ζ • v))⁻¹) 0‖ ≤
      (2 : ℝ)^142000/(globalPoleRadius k)^2 := by
  apply (globalPole_inverse_derivative D hh j k hk hk0 hv n).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hf : (n.factorial : ℝ) ≤ (2 : ℝ)^160 :=
    (show (n.factorial : ℝ) ≤ (Nat.factorial 32 : ℕ) by
      exact_mod_cast Nat.factorial_le (show n ≤ 32 by omega)).trans
      MasterConstants.factorial32_le_power
  calc
    _ ≤ (2 : ℝ)^160 * (2 : ℝ)^(8211+8327*n) :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    _ = (2 : ℝ)^(160+(8211+8327*n)) := (pow_add (2 : ℝ) 160 (8211+8327*n)).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

end Maxwell.Continuum.PeriodicBand
