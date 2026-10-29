import Maxwell.Continuum.AlmostAnalyticPhase

/-! Quantitative Fourier decay from the full contour identity. The
analytic symbol is operator-valued; only its actual tube and transition
shell bounds enter the two terms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary MasterConstants MeasureTheory Set Metric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def phasedSymbol (R : Space) (Y : Momentum → F) (q : Momentum) : F :=
  complexPhase R q • Y q

omit [CompleteSpace F] in
theorem phasedSymbol_analyticAt (R : Space) {Y : Momentum → F} {q : Momentum}
    (hY : AnalyticAt ℂ Y q) : AnalyticAt ℂ (phasedSymbol R Y) q :=
  (complexPhase_analytic R q).smul hY

omit [CompleteSpace F] in
theorem phasedSymbol_shifted_norm (R β q : Space) (Y : Momentum → F) (s : ℝ) :
    ‖phasedSymbol R Y (shiftedMomentum q β s)‖ =
      Real.exp (-s*inner ℝ β R) * ‖Y (shiftedMomentum q β s)‖ := by
  rw [phasedSymbol, norm_smul, complexPhase_shifted_norm]

omit [CompleteSpace F] in
theorem shifted_integral_bound {β : Space} (hβ0 : β ≠ 0) (R : Space)
    (Y : Momentum → F) {M : ℝ} (hM : 0 ≤ M)
    (hY : ∀ q, ‖q‖ ≤ 4*smallRadius → ‖Y (shiftedMomentum q β 1)‖ ≤ M) :
    ‖∫ q, contourProduct (cutoffOrder β) β (phasedSymbol R Y) 1 q‖ ≤
      (2 : ℝ)^49 * M * Real.exp (-inner ℝ β R) := by
  have hsmall : 4*smallRadius ≤ (1 : ℝ) := by
    norm_num [smallRadius, backgroundAmplitude]
  have hsupp : Function.support (contourProduct (cutoffOrder β) β (phasedSymbol R Y) 1) ⊆
      closedBall (0 : Space) 1 := by
    intro q hq
    have hb := contourProduct_tsupport (cutoffOrder β) β (phasedSymbol R Y) 1 (subset_closure hq)
    have hn : ‖q‖ ≤ 4*smallRadius := by simpa only [mem_closedBall, dist_zero_right] using hb
    simpa only [mem_closedBall, dist_zero_right] using hn.trans hsmall
  have hbound (q : Space) :
      ‖contourProduct (cutoffOrder β) β (phasedSymbol R Y) 1 q‖ ≤
        (2 : ℝ)^46 * (Real.exp (-inner ℝ β R)*M) := by
    by_cases hq : ‖q‖ ≤ 4*smallRadius
    · rw [contourProduct, norm_smul, phasedSymbol_shifted_norm, neg_mul, one_mul]
      exact mul_le_mul (cutoffTaylor_norm_le hβ0 q (by norm_num))
        (mul_le_mul_of_nonneg_left (hY q hq) (Real.exp_pos _).le) (by positivity) (by positivity)
    · rw [contourProduct_zero_outside _ β _ 1 (lt_of_not_ge hq), norm_zero]
      positivity
  apply (integral_norm_compact_le _ (by positivity) hsupp hbound).trans_eq
  ring

omit [CompleteSpace F] in
theorem initial_integral_eq (K : ℕ) (β R : Space) (Y : Momentum → F) :
    (∫ q, contourProduct K β (phasedSymbol R Y) 0 q) =
      OperatorFourier.angularFourier
        (fun q => (Well.chi smallRadius q : ℂ) • Y (realMomentumMap q)) (-R) := by
  rw [OperatorFourier.angularFourier_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    rw [contourProduct_at_zero, phasedSymbol, complexPhase_real, smul_comm]

theorem cutoff_fourier_bound_nonzero {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) (R : Space) (hphase : 0 ≤ inner ℝ β R)
    (Y : Momentum → F) {M M₀ : ℝ} (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (hYa : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ Y (shiftedMomentum q β s))
    (hYb : ∀ q, ‖q‖ ≤ 4*smallRadius → ‖Y (shiftedMomentum q β 1)‖ ≤ M)
    (hYs : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q : Space, smallRadius ≤ ‖q‖ →
      ‖q‖ ≤ 4*smallRadius → ‖Y (shiftedMomentum q β s)‖ ≤ M₀) :
    ‖OperatorFourier.angularFourier
        (fun q => (Well.chi smallRadius q : ℂ) • Y (realMomentumMap q)) (-R)‖ ≤
      (2 : ℝ)^49 * M * Real.exp (-inner ℝ β R) +
        (2 : ℝ)^49 * M₀ * Real.exp (-cs*L) := by
  have ha : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ (phasedSymbol R Y) (shiftedMomentum q β s) := by
    intro s hs q hq
    exact phasedSymbol_analyticAt R (hYa s hs q hq)
  have hb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q : Space, smallRadius ≤ ‖q‖ →
      ‖q‖ ≤ 4*smallRadius → ‖phasedSymbol R Y (shiftedMomentum q β s)‖ ≤ M₀ := by
    intro s hs q hq hq'
    rw [phasedSymbol_shifted_norm]
    have he : Real.exp (-s*inner ℝ β R) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hs.1, hphase])
    exact (mul_le_mul he (hYs s hs q hq hq') (norm_nonneg _) (by norm_num)).trans_eq (one_mul M₀)
  have herr := contour_integral_error_bound hL hβ hβ0 (phasedSymbol R Y) hM₀ ha hb
  have hshift := shifted_integral_bound hβ0 R Y hM hYb
  rw [← initial_integral_eq (cutoffOrder β) β R Y]
  have htri := norm_sub_le
    (∫ q, contourProduct (cutoffOrder β) β (phasedSymbol R Y) 1 q)
    ((∫ q, contourProduct (cutoffOrder β) β (phasedSymbol R Y) 1 q) -
      (∫ q, contourProduct (cutoffOrder β) β (phasedSymbol R Y) 0 q))
  rw [sub_sub_cancel] at htri
  exact htri.trans (add_le_add hshift herr)

#print axioms cutoff_fourier_bound_nonzero

end Maxwell.Continuum.AlmostAnalytic
