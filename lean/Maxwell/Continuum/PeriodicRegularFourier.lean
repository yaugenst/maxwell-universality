import Maxwell.Continuum.PeriodicRegularSupport
import Maxwell.Continuum.CellSourceAnalytic
import Maxwell.Continuum.OperatorFourierDecay

/-! Global smoothness, compact support, and the actual sixteenfold
Fourier decay of the selected contribution outside the local pole chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary EffectiveMass AlmostAnalytic Set Metric Filter MeasureTheory
open scoped Topology FourierTransform

attribute [local irreducible] selectedPoleNumerator scaledSourceProduct realMode imaginaryPole
  poleMomentum dielectricBand selectedGlobalQuotient

theorem selectedGlobalQuotient_joint_analyticAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖) :
    AnalyticAt ℂ (selectedGlobalQuotient D hh j) (realMomentum k.ofLp) := by
  have hp : (h : ℂ) • (scaledPoleCenter D hh j + realMomentum k.ofLp) ∈ physicalChart := by
    intro i
    exact (norm_le_pi_norm _ i).trans_lt ((globalPole_source_physical D hh j k hk).trans_lt
      (by linarith only [analyticRadius_pos]))
  have hn : AnalyticAt ℂ (selectedPoleNumerator D hh j) (realMomentum k.ofLp) := by
    unfold selectedPoleNumerator
    exact (CellGauge.scaledSourceProduct_joint_analytic D.h_pos (realMode D hh) _ hp).comp
      (f := fun p : Momentum => scaledPoleCenter D hh j + p)
      (analyticAt_const.add analyticAt_id)
  have hchart : poleMomentum D hh j (realMomentum k.ofLp) ∈ physicalChart := by
    rwa [scaledPoleCenter_physical] at hp
  have hm : AnalyticAt ℂ (poleMomentum D hh j) (realMomentum k.ofLp) := by
    unfold poleMomentum
    exact analyticAt_const.add (analyticAt_id.const_smul (c := (h : ℂ)))
  have hd : AnalyticAt ℂ (poleDenominator D hh j) (realMomentum k.ofLp) := by
    unfold poleDenominator
    exact analyticAt_const.mul
      (((dielectricBand_analytic _ hchart).comp (f := poleMomentum D hh j) hm).sub analyticAt_const)
  have hn0 : 0 < ‖k‖ := poleCutoff_scales.2.2.1.trans_le hk0
  have hne : poleDenominator D hh j (realMomentum k.ofLp) ≠ 0 := by
    apply norm_pos_iff.mp
    exact (div_pos (sq_pos_of_pos hn0) (by norm_num)).trans_le
      (globalPole_denominator_norm_lower D hh j k hk)
  unfold selectedGlobalQuotient
  convert! hn.div hd hne using 1

theorem regularSelectedSymbol_contDiff {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (regularSelectedSymbol D hh j) := by
  rw [contDiff_iff_contDiffAt]
  intro k
  by_cases hc : ‖k‖ < poleCoreRadius
  · have hz : regularSelectedSymbol D hh j =ᶠ[𝓝 k] (fun _ => 0) := by
      filter_upwards [continuous_norm.continuousAt.eventually (eventually_lt_nhds hc)] with p hp
      exact regularSelectedSymbol_zero_core D hh j hp.le
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · by_cases hk : h*‖k‖ ≤ 4*smallRadius
    · have hq := selectedGlobalQuotient_joint_analyticAt D hh j k hk (le_of_not_gt hc)
      have hr : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun p : Space => selectedGlobalQuotient D hh j (realMomentum p.ofLp)) k :=
        (hq.contDiffAt.restrict_scalars ℝ).comp k realMomentumMap.contDiff.contDiffAt
      exact (contDiff_const.sub (poleChartCutoff_contDiff j)).contDiffAt.smul
        ((scaledPoleCutoff_contDiff D hh j).contDiffAt.mul hr)
    · have hz : regularSelectedSymbol D hh j =ᶠ[𝓝 k] (fun _ => 0) := by
        have hcont : ContinuousAt (fun p : Space => h*‖p‖) k := by fun_prop
        filter_upwards [hcont.eventually (eventually_gt_nhds (lt_of_not_ge hk))] with p hp
        exact regularSelectedSymbol_zero_outside D hh j hp
      exact contDiffAt_const.congr_of_eventuallyEq hz

theorem regularSelectedSymbol_tsupport {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    tsupport (regularSelectedSymbol D hh j) ⊆ closedBall (0 : Space) (4*smallRadius/h) := by
  apply closure_minimal _ isClosed_closedBall
  intro k hk
  rw [mem_closedBall, dist_zero_right]
  by_contra hn
  have hlt : 4*smallRadius < h*‖k‖ := by
    have he := (div_lt_iff₀ D.h_pos).mp (lt_of_not_ge hn)
    simpa only [mul_comm] using he
  exact Function.mem_support.mp hk (regularSelectedSymbol_zero_outside D hh j hlt)

theorem regularSelectedSymbol_compact {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    HasCompactSupport (regularSelectedSymbol D hh j) :=
  (isCompact_closedBall (0 : Space) (4*smallRadius/h)).of_isClosed_subset isClosed_closure
    (regularSelectedSymbol_tsupport D hh j)

theorem regularSelectedSymbol_integrable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    Integrable (regularSelectedSymbol D hh j) volume :=
  (regularSelectedSymbol_contDiff D hh j).continuous.integrable_of_hasCompactSupport
    (regularSelectedSymbol_compact D hh j)

theorem regularSelectedSymbol_fourier_weighted {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    |T|^16 * ‖OperatorFourier.angularFourier (regularSelectedSymbol D hh j)
      (T • PiLp.single 2 j 1)‖ ≤ (2 : ℝ)^220000*h⁻¹ := by
  let v : Space := PiLp.single 2 j 1
  have hv : ‖v‖ = 1 := by simp only [v, PiLp.norm_single, norm_one]
  have he : 2*Real.pi*|inner ℝ ((2*Real.pi)⁻¹ • (T • v)) v| = |T| := by
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, one_pow,
      mul_one, abs_mul, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
    field_simp
  have hb := OperatorFourier.fourier_directional_le (regularSelectedSymbol D hh j)
    (regularSelectedSymbol_contDiff D hh j) (regularSelectedSymbol_compact D hh j)
    16 ((2*Real.pi)⁻¹ • (T • v)) v
  rw [he] at hb
  apply hb.trans
  simp only [OperatorFourier.directionalDerivative_eq_line _ _ (regularSelectedSymbol_contDiff D hh j)]
  exact regularSelectedSymbol_derivative_integral D hh j (n := 16) le_rfl

theorem regularSelectedSymbol_fourier_decay {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖OperatorFourier.angularFourier (regularSelectedSymbol D hh j)
      (T • PiLp.single 2 j 1)‖ ≤ (2 : ℝ)^220000*h⁻¹/T^16 := by
  apply (le_div_iff₀ (pow_pos hT 16)).mpr
  simpa only [abs_of_pos hT, mul_comm] using regularSelectedSymbol_fourier_weighted D hh j T

#print axioms regularSelectedSymbol_fourier_decay

end Maxwell.Continuum.PeriodicBand
