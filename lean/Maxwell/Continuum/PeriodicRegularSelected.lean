import Maxwell.Continuum.PeriodicGlobalQuotient
import Maxwell.Continuum.PeriodicScaledCutoff
import Maxwell.Continuum.PoleChartCutoffLongitudinal

/-! The actual selected contribution outside the fixed local pole
chart, including the literal shifted cutoff and its longitudinal
derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary AlmostAnalytic Set Metric Filter
open scoped Topology

attribute [local irreducible] selectedGlobalQuotient poleDenominator selectedPoleNumerator

theorem realMomentum_longitudinal_line (j : Fin 3) (k : Space) (t : ℝ) :
    realMomentum (k+t • PiLp.single 2 j 1).ofLp =
      realMomentum k.ofLp + (t : ℂ) • basisVector j := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [realMomentum, basisVector]
  · simp [realMomentum, basisVector, hij]

theorem selectedGlobalQuotient_real_line_contDiffAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => selectedGlobalQuotient D hh j
      (realMomentum (k+t • PiLp.single 2 j 1).ofLp)) 0 := by
  simp only [realMomentum_longitudinal_line]
  have ha := selectedGlobalQuotient_line_analyticAt D hh j k hk hk0 (basisVector_norm j).le
  have hc : ContDiffAt ℂ (⊤ : ℕ∞)
      (fun ζ : ℂ => selectedGlobalQuotient D hh j (realMomentum k.ofLp + ζ • basisVector j)) 0 :=
    ha.contDiffAt
  convert! ContDiffAt.comp (f := fun t : ℝ => (t : ℂ)) (0 : ℝ)
    (hc.restrict_scalars ℝ) Complex.ofRealCLM.contDiff.contDiffAt using 1

def cutoffSelectedQuotient {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space) : ℂ :=
  scaledPoleCutoff D hh j k * selectedGlobalQuotient D hh j (realMomentum k.ofLp)

theorem cutoffSelectedQuotient_line_contDiffAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      cutoffSelectedQuotient D hh j (k+t • PiLp.single 2 j 1)) 0 := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      scaledPoleCutoff D hh j (k+t • PiLp.single 2 j 1)) :=
    (scaledPoleCutoff_contDiff D hh j).comp (by fun_prop)
  exact hc.contDiffAt.mul (selectedGlobalQuotient_real_line_contDiffAt D hh j k hk hk0)

theorem cutoffSelectedQuotient_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖)
    {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ =>
      cutoffSelectedQuotient D hh j (k+t • PiLp.single 2 j 1)) 0‖ ≤
      (2 : ℝ)^149000/(globalPoleRadius k)^2 := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      scaledPoleCutoff D hh j (k+t • PiLp.single 2 j 1)) :=
    (scaledPoleCutoff_contDiff D hh j).comp (by fun_prop)
  have he := BoundedLeibniz.mul_derivative_le (n := n) (x := (0 : ℝ))
    (A := (2 : ℝ)^5261) (B := (2 : ℝ)^143000/(globalPoleRadius k)^2) (by positivity)
    (hc.contDiffAt.of_le (by simp))
    ((selectedGlobalQuotient_real_line_contDiffAt D hh j k hk hk0).of_le (by simp))
    (fun i hi => scaledPoleCutoff_derivative D hh j k (PiLp.single 2 j 1)
      (by simp only [PiLp.norm_single, norm_one, le_refl]) (by omega : i ≤ 32))
    (fun i hi => by
      simp only [realMomentum_longitudinal_line]
      exact selectedGlobalQuotient_real_derivative D hh j k hk hk0
        (basisVector_norm j).le (hi.trans hn))
  apply he.trans
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [← pow_add, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

def regularSelectedSymbol {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space) : ℂ :=
  (1-poleChartCutoff j k) • cutoffSelectedQuotient D hh j k

theorem regularSelectedSymbol_derivative_outside {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖)
    {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ =>
      regularSelectedSymbol D hh j (k+t • PiLp.single 2 j 1)) 0‖ ≤
      (2 : ℝ)^220000/(globalPoleRadius k)^2 := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => 1-poleChartCutoff j (k+t • PiLp.single 2 j 1)) :=
    contDiff_const.sub ((poleChartCutoff_contDiff j).comp (by fun_prop))
  have he := BoundedLeibniz.real_smul_derivative_le (n := n) (x := (0 : ℝ))
    (A := (2 : ℝ)^70000) (B := (2 : ℝ)^149000/(globalPoleRadius k)^2) (by positivity)
    (hc.contDiffAt.of_le (by simp))
    ((cutoffSelectedQuotient_line_contDiffAt D hh j k hk hk0).of_le (by simp))
    (fun i hi => poleChartComplement_longitudinal_bound j k (hi.trans hn) 0)
    (fun i hi => cutoffSelectedQuotient_derivative D hh j k hk hk0 (hi.trans hn))
  apply he.trans
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [← pow_add, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem regularSelectedSymbol_zero_core {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space} (hk : ‖k‖ ≤ poleCoreRadius) :
    regularSelectedSymbol D hh j k = 0 := by
  rw [regularSelectedSymbol, poleChartCutoff_core j hk, sub_self, zero_smul]

theorem regularSelectedSymbol_derivative_core {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Space} (hk : ‖k‖ < poleCoreRadius) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => regularSelectedSymbol D hh j (k+t • PiLp.single 2 j 1)) 0 = 0 := by
  have hm : ∀ᶠ t : ℝ in 𝓝 0, ‖k+t • PiLp.single 2 j 1‖ < poleCoreRadius := by
    have hc : ContinuousAt (fun t : ℝ => ‖k+t • PiLp.single 2 j 1‖) 0 := by fun_prop
    exact hc.eventually (by simpa only [zero_smul, add_zero] using eventually_lt_nhds hk)
  have he : (fun t : ℝ => regularSelectedSymbol D hh j (k+t • PiLp.single 2 j 1)) =ᶠ[𝓝 0]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hm] with t ht
    exact regularSelectedSymbol_zero_core D hh j ht.le
  rw [he.iteratedDeriv_eq n]
  simp only [iteratedDeriv_const, ite_self]

end Maxwell.Continuum.PeriodicBand
