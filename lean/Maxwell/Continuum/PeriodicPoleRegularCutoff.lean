import Maxwell.Continuum.OscillatoryHolomorphicCutoff
import Maxwell.Continuum.PoleChartCutoffLongitudinal
import Maxwell.Continuum.PoleTailLedger
import Maxwell.Continuum.PeriodicPoleRegularDerivatives

/-! Actual sixteenfold integration by parts for the regular local part. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian OscillatoryPole
open scoped ContDiff

attribute [local irreducible] selectedRegularPart

theorem regularCutoff_radius : 2*poleLongitudinalScale < longitudinalPoleRadius/8 := by
  norm_num [poleLongitudinalScale, longitudinalPoleRadius]

theorem selectedRegularCutoff_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    AnalyticOnNhd ℂ (selectedRegularPart D hh j w) (closedBall 0 (longitudinalPoleRadius/8)) := by
  intro u hu
  apply selectedRegularPart_analytic D hh j hw
  have hu' : ‖u‖ ≤ longitudinalPoleRadius/8 := by simpa only [mem_closedBall, dist_zero_right] using hu
  exact hu'.trans (by linarith only [pole_radii.1])

theorem selectedRegularPart_derivative_ledger {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius/8) {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (selectedRegularPart D hh j w) u‖ ≤ (2 : ℝ)^17587 := by
  calc
    _ ≤ (n.factorial : ℝ)*(2 : ℝ)^(1091+1027*n) := selectedRegularPart_iteratedDeriv D hh j hw hu n
    _ ≤ (2 : ℝ)^64*2^17523 := mul_le_mul (poleTail_factorial hn)
      (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]

theorem selectedRegularCutoff_jet_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {n : ℕ} (hn : n ≤ 16) {u : ℝ} (hu : |u| ≤ 2*poleLongitudinalScale) :
    ‖iteratedDeriv n (cutoffHolomorphic poleLongitudinalScale (selectedRegularPart D hh j w)) u‖ ≤
      (2 : ℝ)^51000 := by
  rw [cutoffHolomorphic_jets regularCutoff_radius.le (selectedRegularCutoff_analytic D hh j hw) hu n]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1),
        ‖(n.choose k : ℂ)*((iteratedDeriv k (scaledPsi poleLongitudinalScale) u : ℝ) : ℂ)*
          iteratedDeriv (n-k) (selectedRegularPart D hh j w) (u : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n+1), (2 : ℝ)^50663 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hc : (n.choose k : ℝ) ≤ (2 : ℝ)^16 :=
        (show (n.choose k : ℝ) ≤ (2 : ℝ)^n by exact_mod_cast Nat.choose_le_two_pow n k).trans
          (pow_le_pow_right₀ (by norm_num) hn)
      have hf := selectedRegularPart_derivative_ledger D hh j hw
        (u := (u : ℂ)) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu.trans regularCutoff_radius.le)
        ((Nat.sub_le n k).trans hn)
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ (2 : ℝ)^16*2^33060*2^17587 := by
          gcongr
          exact poleLongitudinal_derivative_bound (hkn.trans hn) u
        _ = _ := by rw [← pow_add, ← pow_add]
    _ = (n+1 : ℝ)*2^50663 := by simp
    _ ≤ 2^5*2^50663 := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show n+1≤2^5 by omega)) (by positivity)
    _ = (2 : ℝ)^50668 := by rw [← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num)

theorem selectedRegularCutoff_oscillatory_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {T : ℝ} (hT : 0 < T) :
    ‖∫u : ℝ, oscillatoryPhase T u*
      cutoffHolomorphic poleLongitudinalScale (selectedRegularPart D hh j w) u‖ ≤
        (2 : ℝ)^51002/T^16 := by
  have hb := cutoffHolomorphic_oscillatory_bound poleCutoff_scales.1 regularCutoff_radius
    (selectedRegularCutoff_analytic D hh j hw) 16 (by positivity : (0 : ℝ) ≤ 2^51000)
    (fun u hu => selectedRegularCutoff_jet_bound D hh j hw (by omega : 16≤16) hu) hT
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ 4*1*(2 : ℝ)^51000 := by
      gcongr
      norm_num [poleLongitudinalScale]
    _ = _ := by rw [mul_one, show (4 : ℝ)=2^2 by norm_num, ← pow_add]

#print axioms selectedRegularCutoff_oscillatory_bound

end Maxwell.Continuum.PeriodicBand
