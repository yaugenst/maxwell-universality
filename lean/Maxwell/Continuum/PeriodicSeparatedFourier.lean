import Maxwell.Continuum.PeriodicSeparatedCutoff

/-! The actual integrated and Fourier remainder estimates for all
other bands, including continuum source normalization and full cell operators. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary EffectiveMass CellGauge AlmostAnalytic Set Metric Filter MeasureTheory
open scoped Topology FourierTransform

theorem separatedRegularSymbol_derivative_outside {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) {k : Space}
    (hk : 4*smallRadius < h*‖k‖) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => separatedRegularSymbol D hh j u v
      (k+t • PiLp.single 2 j 1)) 0 = 0 := by
  have hm : ∀ᶠ t : ℝ in 𝓝 0, 4*smallRadius < h*‖k+t • PiLp.single 2 j 1‖ := by
    have hc : ContinuousAt (fun t : ℝ => h*‖k+t • PiLp.single 2 j 1‖) 0 := by fun_prop
    exact hc.eventually (by simpa only [zero_smul, add_zero] using eventually_gt_nhds hk)
  have he : (fun t : ℝ => separatedRegularSymbol D hh j u v (k+t • PiLp.single 2 j 1)) =ᶠ[𝓝 0]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hm] with t ht
    exact separatedRegularSymbol_zero_outside D hh j u v ht
  rw [he.iteratedDeriv_eq n]
  simp only [iteratedDeriv_const, ite_self]

theorem separatedRegularSymbol_derivative_global {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k : Space) {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ => separatedRegularSymbol D hh j u v
      (k+t • PiLp.single 2 j 1)) 0‖ ≤ (2 : ℝ)^7000*h^2 := by
  by_cases hk : h*‖k‖ ≤ 4*smallRadius
  · exact separatedRegularSymbol_derivative_inside D hh j hu hv k hk hn
  · rw [separatedRegularSymbol_derivative_outside D hh j u v (lt_of_not_ge hk), norm_zero]
    positivity

theorem separatedRegularSymbol_derivative_majorant {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) {k : Space} (hk0 : k ≠ 0) {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ => separatedRegularSymbol D hh j u v
      (k+t • PiLp.single 2 j 1)) 0‖ ≤ regularSelectedMajorant h k := by
  by_cases hk : k ∈ ball (0 : Space) (5*smallRadius/h)
  · rw [regularSelectedMajorant, Set.indicator_of_mem hk]
    have hnorm : 0 < ‖k‖ := norm_pos_iff.mpr hk0
    have hk' : ‖k‖ < 5*smallRadius/h := by simpa only [mem_ball, dist_zero_right] using hk
    have hb : h*‖k‖ ≤ 1 := by
      have he := (lt_div_iff₀ D.h_pos).mp hk'
      have hs : 5*smallRadius ≤ (1 : ℝ) := by norm_num [smallRadius, backgroundAmplitude]
      have he' : h*‖k‖ ≤ 5*smallRadius := by simpa only [mul_comm] using he.le
      exact he'.trans hs
    have hi : h^2 ≤ (‖k‖^2)⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ (sq_pos_of_pos hnorm)).mpr
      have hs := pow_le_pow_left₀ (mul_nonneg D.h_pos.le hnorm.le) hb 2
      simpa only [mul_pow, one_pow] using hs
    apply (separatedRegularSymbol_derivative_global D hh j hu hv k hn).trans
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega : 7000 ≤ 220000)) hi
      (sq_nonneg h) (by positivity)
  · rw [regularSelectedMajorant, Set.indicator_of_notMem hk]
    have hn' : 5*smallRadius/h ≤ ‖k‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hk
    have hm : 5*smallRadius ≤ h*‖k‖ := by
      have he := (div_le_iff₀ D.h_pos).mp hn'
      simpa only [mul_comm] using he
    rw [separatedRegularSymbol_derivative_outside D hh j u v
      (lt_of_lt_of_le (by linarith only [smallRadius_pos]) hm), norm_zero]

theorem separatedRegularSymbol_derivative_integral {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) {n : ℕ} (hn : n ≤ 16) :
    (∫ k : Space, ‖iteratedDeriv n (fun t : ℝ =>
      separatedRegularSymbol D hh j u v (k+t • PiLp.single 2 j 1)) 0‖) ≤
      (2 : ℝ)^220000*h⁻¹ := by
  apply le_trans _ (regularSelectedMajorant_integral D.h_pos)
  apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => norm_nonneg _))
    (regularSelectedMajorant_integrable h)
  filter_upwards [volume.ae_ne (0 : Space)] with k hk
  exact separatedRegularSymbol_derivative_majorant D hh j hu hv hk hn

theorem separatedRegularSymbol_integrable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) :
    Integrable (separatedRegularSymbol D hh j u v) volume :=
  (separatedRegularSymbol_contDiff D hh j u v).continuous.integrable_of_hasCompactSupport
    (separatedRegularSymbol_compact D hh j u v)

theorem separatedRegularSymbol_fourier_weighted {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (T : ℝ) :
    |T|^16 * ‖OperatorFourier.angularFourier (separatedRegularSymbol D hh j u v)
      (T • PiLp.single 2 j 1)‖ ≤ (2 : ℝ)^220000*h⁻¹ := by
  let w : Space := PiLp.single 2 j 1
  have hw : ‖w‖ = 1 := by simp only [w, PiLp.norm_single, norm_one]
  have he : 2*Real.pi*|inner ℝ ((2*Real.pi)⁻¹ • (T • w)) w| = |T| := by
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hw, one_pow,
      mul_one, abs_mul, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
    field_simp
  have hb := OperatorFourier.fourier_directional_le (separatedRegularSymbol D hh j u v)
    (separatedRegularSymbol_contDiff D hh j u v) (separatedRegularSymbol_compact D hh j u v)
    16 ((2*Real.pi)⁻¹ • (T • w)) w
  rw [he] at hb
  apply hb.trans
  simp only [OperatorFourier.directionalDerivative_eq_line _ _
    (separatedRegularSymbol_contDiff D hh j u v)]
  exact separatedRegularSymbol_derivative_integral D hh j hu hv (n := 16) le_rfl

theorem separatedRegularSymbol_fourier_decay {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) {T : ℝ} (hT : 0 < T) :
    ‖OperatorFourier.angularFourier (separatedRegularSymbol D hh j u v)
      (T • PiLp.single 2 j 1)‖ ≤ (2 : ℝ)^220000*h⁻¹/T^16 := by
  apply (le_div_iff₀ (pow_pos hT 16)).mpr
  simpa only [abs_of_pos hT, mul_comm] using separatedRegularSymbol_fourier_weighted D hh j hu hv T

#print axioms separatedRegularSymbol_fourier_decay

end Maxwell.Continuum.PeriodicBand
