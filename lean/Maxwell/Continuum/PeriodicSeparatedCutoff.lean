import Maxwell.Continuum.PeriodicSeparatedSource
import Maxwell.Continuum.PeriodicRegularFourier

/-! The actual cutoff other-band source symbol, with its first sixteen
longitudinal derivatives and global smooth compact extension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary EffectiveMass CellGauge AlmostAnalytic Set Metric Filter
open scoped Topology

attribute [local irreducible] separatedSourceSymbol

theorem separatedSourceSymbol_real_contDiffAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space => separatedSourceSymbol D hh j u v
      (realMomentum p.ofLp)) k := by
  have hp := globalPole_unit_line_chart D hh j k hk (v := (0 : Momentum)) (by simp)
    (ζ := (0 : ℂ)) (by norm_num)
  simp only [zero_smul, add_zero] at hp
  exact ((separatedSourceSymbol_analyticAt D hh j u v hp).contDiffAt.restrict_scalars ℝ).comp k
    realMomentumMap.contDiff.contDiffAt

theorem separatedSourceSymbol_real_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k : Space) (hk : h*‖k‖ ≤ 4*smallRadius)
    {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ => separatedSourceSymbol D hh j u v
      (realMomentum (k+t • PiLp.single 2 j 1).ofLp)) 0‖ ≤ (2 : ℝ)^1400*h^2 := by
  simp only [realMomentum_longitudinal_line]
  rw [OperatorFourier.iteratedDeriv_restrict_complex _ (ball 0 (1/16)) isOpen_ball
    ((separatedSourceSymbol_line_analytic D hh j u v k hk (basisVector_norm j).le).mono
      ball_subset_closedBall) n 0 (by simp only [mem_ball, Complex.ofReal_zero, dist_self]; norm_num)]
  exact separatedSourceSymbol_derivative D hh j hu hv k hk (basisVector_norm j).le hn

def separatedRegularSymbol {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) (k : Space) : ℂ :=
  ((64*blochDensity : ℝ) : ℂ)*(scaledPoleCutoff D hh j k*
    separatedSourceSymbol D hh j u v (realMomentum k.ofLp))

theorem separatedRegularSymbol_zero_outside {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) {k : Space}
    (hk : 4*smallRadius < h*‖k‖) : separatedRegularSymbol D hh j u v k = 0 := by
  rw [separatedRegularSymbol, scaledPoleCutoff_zero_outside D hh j hk, zero_mul, mul_zero]

theorem separatedRegularSymbol_contDiff {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) :
    ContDiff ℝ (⊤ : ℕ∞) (separatedRegularSymbol D hh j u v) := by
  rw [contDiff_iff_contDiffAt]
  intro k
  by_cases hk : h*‖k‖ ≤ 4*smallRadius
  · exact contDiffAt_const.mul ((scaledPoleCutoff_contDiff D hh j).contDiffAt.mul
      (separatedSourceSymbol_real_contDiffAt D hh j u v k hk))
  · have hz : separatedRegularSymbol D hh j u v =ᶠ[𝓝 k] (fun _ => 0) := by
      have hcont : ContinuousAt (fun p : Space => h*‖p‖) k := by fun_prop
      filter_upwards [hcont.eventually (eventually_gt_nhds (lt_of_not_ge hk))] with p hp
      exact separatedRegularSymbol_zero_outside D hh j u v hp
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem separatedRegularSymbol_tsupport {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) :
    tsupport (separatedRegularSymbol D hh j u v) ⊆ closedBall (0 : Space) (4*smallRadius/h) := by
  apply closure_minimal _ isClosed_closedBall
  intro k hk
  rw [mem_closedBall, dist_zero_right]
  by_contra hn
  have hlt : 4*smallRadius < h*‖k‖ := by
    have he := (div_lt_iff₀ D.h_pos).mp (lt_of_not_ge hn)
    simpa only [mul_comm] using he
  exact Function.mem_support.mp hk (separatedRegularSymbol_zero_outside D hh j u v hlt)

theorem separatedRegularSymbol_compact {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) :
    HasCompactSupport (separatedRegularSymbol D hh j u v) :=
  (isCompact_closedBall (0 : Space) (4*smallRadius/h)).of_isClosed_subset isClosed_closure
    (separatedRegularSymbol_tsupport D hh j u v)

theorem separatedRegularSymbol_derivative_inside {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k : Space) (hk : h*‖k‖ ≤ 4*smallRadius)
    {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ => separatedRegularSymbol D hh j u v
      (k+t • PiLp.single 2 j 1)) 0‖ ≤ (2 : ℝ)^7000*h^2 := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      scaledPoleCutoff D hh j (k+t • PiLp.single 2 j 1)) :=
    (scaledPoleCutoff_contDiff D hh j).comp (by fun_prop)
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => separatedSourceSymbol D hh j u v
      (realMomentum (k+t • PiLp.single 2 j 1).ofLp)) 0 := by
    have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space => separatedSourceSymbol D hh j u v
        (realMomentum p.ofLp)) (k+(0 : ℝ) • PiLp.single 2 j 1) := by
      simpa only [zero_smul, add_zero] using separatedSourceSymbol_real_contDiffAt D hh j u v k hk
    have he := hat.comp (0 : ℝ)
      (show ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => k+t • PiLp.single 2 j 1) 0 by fun_prop)
    simpa only [zero_smul, add_zero, Function.comp_def] using he
  have hb := BoundedLeibniz.mul_derivative_le (n := n) (x := (0 : ℝ))
    (A := (2 : ℝ)^5261) (B := (2 : ℝ)^1400*h^2) (by positivity)
    (hc.contDiffAt.of_le (by simp)) (hs.of_le (by simp))
    (fun i hi => scaledPoleCutoff_derivative D hh j k (PiLp.single 2 j 1)
      (by simp only [PiLp.norm_single, norm_one, le_refl]) (by omega : i ≤ 32))
    (fun i hi => separatedSourceSymbol_real_derivative D hh j hu hv k hk (hi.trans hn))
  have ha : ‖((64*blochDensity : ℝ) : ℂ)‖ ≤ (2 : ℝ)^6 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) blochDensity_pos)]
    have he := mul_le_mul_of_nonneg_left blochDensity_le_one (by norm_num : (0 : ℝ) ≤ 64)
    norm_num at he ⊢
    exact he
  unfold separatedRegularSymbol
  rw [iteratedDeriv_const_mul_field, norm_mul]
  apply (mul_le_mul ha hb (norm_nonneg _) (by positivity)).trans
  have he (a b c d x : ℝ) : a*(b*c*(d*x)) = (a*b*c*d)*x := by ring
  rw [he, ← pow_add, ← pow_add, ← pow_add]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (sq_nonneg h)

#print axioms separatedRegularSymbol_derivative_inside

end Maxwell.Continuum.PeriodicBand
