import Maxwell.Continuum.PeriodicRegularFourier

/-! Absolute integrability at the actual imaginary pole and the exact
split into the local pole contribution and the smooth global remainder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary EffectiveMass AlmostAnalytic Set Metric Filter MeasureTheory
open scoped Topology FourierTransform

attribute [local irreducible] selectedPoleNumerator scaledSourceProduct realMode imaginaryPole
  poleMomentum dielectricBand selectedGlobalQuotient

theorem globalPole_denominator_ne_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space}
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : k ≠ 0) :
    poleDenominator D hh j (realMomentum k.ofLp) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (div_pos (sq_pos_of_pos (norm_pos_iff.mpr hk0)) (by norm_num)).trans_le
    (globalPole_denominator_norm_lower D hh j k hk)

theorem selectedGlobalQuotient_real_continuousAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space}
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : k ≠ 0) :
    ContinuousAt (fun p : Space => selectedGlobalQuotient D hh j (realMomentum p.ofLp)) k := by
  have hp : (h : ℂ) • (scaledPoleCenter D hh j + realMomentum k.ofLp) ∈ physicalChart := by
    intro i
    exact (norm_le_pi_norm _ i).trans_lt ((globalPole_source_physical D hh j k hk).trans_lt
      (by linarith only [analyticRadius_pos]))
  have hn : ContinuousAt (fun p : Space => selectedPoleNumerator D hh j (realMomentum p.ofLp)) k := by
    unfold selectedPoleNumerator
    exact (CellGauge.scaledSourceProduct_joint_analytic D.h_pos (realMode D hh) _ hp).continuousAt.comp
      (f := fun p : Space => scaledPoleCenter D hh j+realMomentumMap p)
      (continuous_const.add realMomentumMap.continuous).continuousAt
  have hchart : poleMomentum D hh j (realMomentum k.ofLp) ∈ physicalChart := by
    rwa [scaledPoleCenter_physical] at hp
  have hm : Continuous (fun p : Space => poleMomentum D hh j (realMomentum p.ofLp)) := by
    unfold poleMomentum
    exact continuous_const.add (realMomentumMap.continuous.const_smul (h : ℂ))
  have hd : ContinuousAt (fun p : Space => poleDenominator D hh j (realMomentum p.ofLp)) k := by
    unfold poleDenominator
    exact continuousAt_const.mul
      (((dielectricBand_analytic _ hchart).continuousAt.comp
        (f := fun p : Space => poleMomentum D hh j (realMomentum p.ofLp)) hm.continuousAt).sub continuousAt_const)
  unfold selectedGlobalQuotient
  exact hn.div hd (globalPole_denominator_ne_zero D hh j hk hk0)

theorem cutoffSelectedQuotient_zero_outside {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space}
    (hk : 4*smallRadius < h*‖k‖) : cutoffSelectedQuotient D hh j k = 0 := by
  rw [cutoffSelectedQuotient, scaledPoleCutoff_zero_outside D hh j hk, zero_mul]

theorem cutoffSelectedQuotient_continuousAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space} (hk0 : k ≠ 0) :
    ContinuousAt (cutoffSelectedQuotient D hh j) k := by
  by_cases hk : h*‖k‖ ≤ 4*smallRadius
  · exact (scaledPoleCutoff_contDiff D hh j).continuous.continuousAt.mul
      (selectedGlobalQuotient_real_continuousAt D hh j hk hk0)
  · have hz : cutoffSelectedQuotient D hh j =ᶠ[𝓝 k] (fun _ => 0) := by
      have hc : ContinuousAt (fun p : Space => h*‖p‖) k := by fun_prop
      filter_upwards [hc.eventually (eventually_gt_nhds (lt_of_not_ge hk))] with p hp
      exact cutoffSelectedQuotient_zero_outside D hh j hp
    exact continuousAt_const.congr_of_eventuallyEq hz

theorem cutoffSelectedQuotient_stronglyMeasurable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    StronglyMeasurable (cutoffSelectedQuotient D hh j) := by
  apply ContinuousOn.stronglyMeasurable_of_countable_compl (s := ({0} : Set Space)ᶜ)
  · intro k hk
    exact (cutoffSelectedQuotient_continuousAt D hh j hk).continuousWithinAt
  · simpa only [compl_compl] using countable_singleton (0 : Space)

theorem cutoffSelectedQuotient_inverseSquare_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space}
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : k ≠ 0) :
    ‖cutoffSelectedQuotient D hh j k‖ ≤ (2 : ℝ)^220000*(‖k‖^2)⁻¹ := by
  have hn : ‖selectedPoleNumerator D hh j (realMomentum k.ofLp)‖ ≤ (2 : ℝ)^352 := by
    have he := globalPole_source_derivative D hh j k hk (v := (0 : Momentum)) (by simp)
      (n := 0) (by omega)
    simpa only [iteratedDeriv_zero, zero_smul, add_zero] using he
  have hc : ‖scaledPoleCutoff D hh j k‖ ≤ (2 : ℝ)^5261 := by
    have he := scaledPoleCutoff_derivative D hh j k (0 : Space) (by simp) (n := 0) (by omega)
    simpa only [iteratedDeriv_zero, zero_smul, add_zero] using he
  have hd := globalPole_denominator_norm_lower D hh j k hk
  have hp : 0 < ‖k‖^2/2 := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hk0)) (by norm_num)
  have hq : ‖selectedGlobalQuotient D hh j (realMomentum k.ofLp)‖ ≤ (2 : ℝ)^352/(‖k‖^2/2) := by
    rw [selectedGlobalQuotient, norm_div]
    exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) hp hd)
  rw [cutoffSelectedQuotient, norm_mul]
  apply (mul_le_mul hc hq (norm_nonneg _) (by positivity)).trans
  rw [div_div_eq_mul_div, ← mul_div_assoc, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sq_nonneg _))
  rw [← pow_succ, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem cutoffSelectedQuotient_majorant {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space} (hk0 : k ≠ 0) :
    ‖cutoffSelectedQuotient D hh j k‖ ≤ regularSelectedMajorant h k := by
  by_cases hk : k ∈ ball (0 : Space) (5*smallRadius/h)
  · rw [regularSelectedMajorant, indicator_of_mem hk]
    by_cases hp : h*‖k‖ ≤ 4*smallRadius
    · exact cutoffSelectedQuotient_inverseSquare_bound D hh j hp hk0
    · rw [cutoffSelectedQuotient_zero_outside D hh j (lt_of_not_ge hp), norm_zero]
      positivity
  · rw [regularSelectedMajorant, indicator_of_notMem hk]
    have hn : 5*smallRadius/h ≤ ‖k‖ := by
      simpa only [mem_ball, dist_zero_right, not_lt] using hk
    have hm : 5*smallRadius ≤ h*‖k‖ := by
      have he := (div_le_iff₀ D.h_pos).mp hn
      simpa only [mul_comm] using he
    rw [cutoffSelectedQuotient_zero_outside D hh j
      (lt_of_lt_of_le (by linarith only [smallRadius_pos]) hm), norm_zero]

theorem cutoffSelectedQuotient_integrable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    Integrable (cutoffSelectedQuotient D hh j) volume := by
  apply (regularSelectedMajorant_integrable h).mono'
    (cutoffSelectedQuotient_stronglyMeasurable D hh j).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : Space)] with k hk
  exact cutoffSelectedQuotient_majorant D hh j hk

def localSelectedSymbol {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space) : ℂ :=
  poleChartCutoff j k • cutoffSelectedQuotient D hh j k

theorem selectedSymbol_local_regular_split {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space) :
    cutoffSelectedQuotient D hh j k =
      localSelectedSymbol D hh j k + regularSelectedSymbol D hh j k := by
  rw [localSelectedSymbol, regularSelectedSymbol, ← add_smul, add_sub_cancel, one_smul]

theorem localSelectedSymbol_integrable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    Integrable (localSelectedSymbol D hh j) volume := by
  convert (cutoffSelectedQuotient_integrable D hh j).sub
    (regularSelectedSymbol_integrable D hh j) using 1
  funext k
  change localSelectedSymbol D hh j k = cutoffSelectedQuotient D hh j k-regularSelectedSymbol D hh j k
  rw [selectedSymbol_local_regular_split]
  exact (add_sub_cancel_right _ _).symm

theorem selectedSymbol_fourier_split {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space) :
    OperatorFourier.angularFourier (cutoffSelectedQuotient D hh j) R =
      OperatorFourier.angularFourier (localSelectedSymbol D hh j) R +
        OperatorFourier.angularFourier (regularSelectedSymbol D hh j) R := by
  have he : cutoffSelectedQuotient D hh j =
      localSelectedSymbol D hh j + regularSelectedSymbol D hh j := by
    funext k
    exact selectedSymbol_local_regular_split D hh j k
  rw [he]
  have hf := congrFun (VectorFourier.fourierIntegral_add (e := Real.fourierChar)
    (μ := (volume : Measure Space)) (L := innerₗ Space) Real.continuous_fourierChar
    (by change Continuous (fun p : Space × Space => inner ℝ p.1 p.2); fun_prop)
    (localSelectedSymbol_integrable D hh j) (regularSelectedSymbol_integrable D hh j))
    ((2*Real.pi)⁻¹ • R)
  simpa only [OperatorFourier.angularFourier, Real.fourier_eq, VectorFourier.fourierIntegral,
    innerₗ_apply_apply, Pi.add_apply] using hf

#print axioms cutoffSelectedQuotient_integrable
#print axioms selectedSymbol_fourier_split

end Maxwell.Continuum.PeriodicBand
