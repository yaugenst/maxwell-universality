import Maxwell.Continuum.PeriodicRegularSelected
import Maxwell.Continuum.WellCoulombSquare

/-! Actual compact support of the regular selected symbol and the
integral bound for its first sixteen longitudinal derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary AlmostAnalytic Set Metric Filter MeasureTheory
open scoped Topology

attribute [local irreducible] selectedGlobalQuotient

theorem scaledPoleCutoff_zero_outside {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space}
    (hk : 4*smallRadius < h*‖k‖) : scaledPoleCutoff D hh j k = 0 := by
  change cutoffTaylor (cutoffOrder (poleContourShift D hh j)) smallRadius
    (h • k) (poleContourShift D hh j) 1 = 0
  apply image_eq_zero_of_notMem_tsupport (f := fun p : Space =>
    cutoffTaylor (cutoffOrder (poleContourShift D hh j)) smallRadius p
      (poleContourShift D hh j) 1)
  intro hm
  have hb := cutoffTaylor_tsupport (cutoffOrder (poleContourShift D hh j))
    (poleContourShift D hh j) 1 hm
  have he : ‖h • k‖ ≤ 4*smallRadius := by
    simpa only [mem_closedBall, dist_zero_right] using hb
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos D.h_pos] at he
  exact hk.not_ge he

theorem regularSelectedSymbol_zero_outside {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space}
    (hk : 4*smallRadius < h*‖k‖) : regularSelectedSymbol D hh j k = 0 := by
  rw [regularSelectedSymbol, cutoffSelectedQuotient, scaledPoleCutoff_zero_outside D hh j hk,
    zero_mul, smul_zero]

theorem regularSelectedSymbol_derivative_outside_support {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space}
    (hk : 4*smallRadius < h*‖k‖) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => regularSelectedSymbol D hh j (k+t • PiLp.single 2 j 1)) 0 = 0 := by
  have hm : ∀ᶠ t : ℝ in 𝓝 0, 4*smallRadius < h*‖k+t • PiLp.single 2 j 1‖ := by
    have hc : ContinuousAt (fun t : ℝ => h*‖k+t • PiLp.single 2 j 1‖) 0 := by fun_prop
    exact hc.eventually (by simpa only [zero_smul, add_zero] using eventually_gt_nhds hk)
  have he : (fun t : ℝ => regularSelectedSymbol D hh j (k+t • PiLp.single 2 j 1)) =ᶠ[𝓝 0]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hm] with t ht
    exact regularSelectedSymbol_zero_outside D hh j ht
  rw [he.iteratedDeriv_eq n]
  simp only [iteratedDeriv_const, ite_self]

theorem regularSelectedSymbol_derivative_global {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ => regularSelectedSymbol D hh j (k+t • PiLp.single 2 j 1)) 0‖ ≤
      (2 : ℝ)^220000*(‖k‖^2)⁻¹ := by
  by_cases hc : ‖k‖ < poleCoreRadius
  · rw [regularSelectedSymbol_derivative_core D hh j hc, norm_zero]
    positivity
  · by_cases hk : h*‖k‖ ≤ 4*smallRadius
    · have hn0 : 0 < ‖k‖ := poleCutoff_scales.2.2.1.trans_le (le_of_not_gt hc)
      apply (regularSelectedSymbol_derivative_outside D hh j k hk (le_of_not_gt hc) hn).trans
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn0)
      apply pow_le_pow_left₀ (norm_nonneg k)
      unfold globalPoleRadius
      linarith
    · rw [regularSelectedSymbol_derivative_outside_support D hh j (lt_of_not_ge hk), norm_zero]
      positivity

def regularSelectedMajorant (h : ℝ) (k : Space) : ℝ :=
  (ball (0 : Space) (5*smallRadius/h)).indicator
    (fun p => (2 : ℝ)^220000*(‖p‖^2)⁻¹) k

theorem regularSelectedMajorant_nonneg (h : ℝ) (k : Space) : 0 ≤ regularSelectedMajorant h k := by
  apply Set.indicator_nonneg
  intro p _
  positivity

theorem regularSelectedMajorant_integrable (h : ℝ) : Integrable (regularSelectedMajorant h) volume := by
  have hi : IntegrableOn (fun p : Space => (2 : ℝ)^220000*(‖p‖^2)⁻¹)
      (ball 0 (5*smallRadius/h)) volume :=
    (Well.inverseSquare_integrable_ball (5*smallRadius/h)).const_mul ((2 : ℝ)^220000)
  exact hi.integrable_indicator measurableSet_ball

theorem regularSelectedSymbol_derivative_majorant {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ => regularSelectedSymbol D hh j (k+t • PiLp.single 2 j 1)) 0‖ ≤
      regularSelectedMajorant h k := by
  by_cases hk : k ∈ ball (0 : Space) (5*smallRadius/h)
  · rw [regularSelectedMajorant, Set.indicator_of_mem hk]
    exact regularSelectedSymbol_derivative_global D hh j k hn
  · rw [regularSelectedMajorant, Set.indicator_of_notMem hk]
    have hn' : 5*smallRadius/h ≤ ‖k‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hk
    have hm : 5*smallRadius ≤ h*‖k‖ := by
      have he := (div_le_iff₀ D.h_pos).mp hn'
      simpa only [mul_comm] using he
    rw [regularSelectedSymbol_derivative_outside_support D hh j
      (lt_of_lt_of_le (by linarith only [smallRadius_pos]) hm), norm_zero]

theorem regularSelectedMajorant_integral {h : ℝ} (hh : 0 < h) :
    (∫ k, regularSelectedMajorant h k) ≤ (2 : ℝ)^220000*h⁻¹ := by
  unfold regularSelectedMajorant
  rw [integral_indicator measurableSet_ball, integral_const_mul,
    Well.inverseSquare_integral_ball _ (div_nonneg (mul_nonneg (by norm_num) smallRadius_pos.le) hh.le)]
  have hr : smallRadius ≤ (1/128 : ℝ) := by norm_num [smallRadius, backgroundAmplitude]
  have hp : 20*Real.pi*smallRadius ≤ 1 := by
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num))
      hr smallRadius_pos.le (by norm_num : (0 : ℝ) ≤ 20*4)
    linarith only [hm]
  calc
    _ = (2 : ℝ)^220000 * ((20*Real.pi*smallRadius)*h⁻¹) := by
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hh.le)).trans_eq (one_mul _)) (by positivity)

theorem regularSelectedSymbol_derivative_integral {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {n : ℕ} (hn : n ≤ 16) :
    (∫ k : Space, ‖iteratedDeriv n (fun t : ℝ =>
      regularSelectedSymbol D hh j (k+t • PiLp.single 2 j 1)) 0‖) ≤ (2 : ℝ)^220000*h⁻¹ := by
  apply le_trans _ (regularSelectedMajorant_integral D.h_pos)
  exact integral_mono_of_nonneg (Eventually.of_forall (fun _ => norm_nonneg _))
    (regularSelectedMajorant_integrable h)
    (Eventually.of_forall (fun k => regularSelectedSymbol_derivative_majorant D hh j k hn))

end Maxwell.Continuum.PeriodicBand
