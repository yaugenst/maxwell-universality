import Maxwell.Green.Jet
import Maxwell.Green.Saddle
import Maxwell.Green.Residue
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Constructing the saddle hypotheses from local analytic estimates. -/

noncomputable section

open Filter Metric Set Complex
open scoped Topology ContDiff

namespace Maxwell.Green

/-- Local Taylor estimates and ordinary continuity produce a genuine smooth
compact transverse cutoff and globally measurable saddle data. -/
theorem exists_localSaddleData_of_local_estimates_with_support
    (a p : ℂ → ℂ) {r ρ v q₁ q₂ K₁ K₃ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hK₁ : 0 < K₁) (hK₃ : 0 < K₃)
    (ha : ContinuousOn a (ball 0 r)) (hp : ContinuousOn p (ball 0 r))
    (hp₀ : p 0 = 0)
    (hamp : ∀ w, ‖w‖ < r → ‖a w - a 0‖ ≤ K₁ * ‖w‖)
    (hphase : ∀ w, ‖w‖ < r → ‖p w - quadraticPhase v q₁ q₂ w‖ ≤ K₃ * ‖w‖ ^ 3) :
    ∃ D : LocalSaddleData,
      HasCompactSupport D.cutoff ∧ D.model = quadraticPhase v q₁ q₂ ∧ D.amplitude0 = a 0 ∧
      (∀ w, D.cutoff w ≠ 0 → D.amplitude w = a w ∧ D.phase w = p w) ∧
      (∀ w, D.cutoff w ≠ 0 → ‖D.phase w‖ ≤ ρ / 2) ∧
      ContDiff ℝ ∞ D.cutoff ∧ (∀ w, D.cutoff w ≠ 0 → ‖w‖ < r) := by
  classical
  let c : ℝ := min q₁ q₂ / (2 * v)
  have hc : 0 < c := div_pos (lt_min hq₁ hq₂) (by positivity)
  have hq (w : ℂ) : c * ‖w‖ ^ 2 ≤ (quadraticPhase v q₁ q₂ w).im := by
    apply quadraticPhase_im_lower hv
    · dsimp [c]
      rw [mul_div_cancel₀ _ (by positivity : 2 * v ≠ 0)]
      exact min_le_left _ _
    · dsimp [c]
      rw [mul_div_cancel₀ _ (by positivity : 2 * v ≠ 0)]
      exact min_le_right _ _
  obtain ⟨s, hs, hpositive⟩ := cubic_perturbation_has_positive_imaginary_part
    hK₃ hr hc hphase hq
  have hpc : ContinuousAt p 0 := hp.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hsmall : ∀ᶠ w in 𝓝 (0 : ℂ), ‖p w‖ < ρ / 2 := by
    have h := hpc.tendsto.eventually (ball_mem_nhds (p 0) (by positivity : 0 < ρ / 2))
    simpa only [mem_ball, hp₀, dist_zero_right] using h
  obtain ⟨t, ht, hsmallBall⟩ := Metric.eventually_nhds_iff.mp hsmall
  let R := min r (min s t)
  have hR : 0 < R := lt_min hr (lt_min hs ht)
  have hRr : R ≤ r := min_le_left _ _
  have hRs : R ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hRt : R ≤ t := (min_le_right _ _).trans (min_le_right _ _)
  let χ : ContDiffBump (0 : ℂ) := ⟨R / 4, R / 2, by positivity, by linarith⟩
  let aext : ℂ → ℂ := (ball 0 r).piecewise a (fun _ => a 0)
  let pext : ℂ → ℂ := (ball 0 r).piecewise p (quadraticPhase v q₁ q₂)
  have hameas : Measurable aext := ha.measurable_piecewise continuousOn_const measurableSet_ball
  have hqcont : Continuous (quadraticPhase v q₁ q₂) := by unfold quadraticPhase; fun_prop
  have hpmeas : Measurable pext := hp.measurable_piecewise hqcont.continuousOn measurableSet_ball
  have hsupport (w : ℂ) (hw : χ w ≠ 0) : ‖w‖ < R := by
    have hmem : w ∈ Function.support χ := hw
    rw [χ.support_eq] at hmem
    have hnorm : ‖w‖ < R / 2 := by simpa only [mem_ball, dist_zero_right] using hmem
    linarith
  have hext (w : ℂ) (hw : χ w ≠ 0) : aext w = a w ∧ pext w = p w := by
    have hin : w ∈ ball 0 r := by
      simpa only [mem_ball, dist_zero_right] using (hsupport w hw).trans_le hRr
    exact ⟨piecewise_eq_of_mem _ _ _ hin, piecewise_eq_of_mem _ _ _ hin⟩
  let D : LocalSaddleData := {
    cutoff := χ
    amplitude := aext
    phase := pext
    model := quadraticPhase v q₁ q₂
    amplitude0 := a 0
    c := c / 2
    K₁ := K₁
    K₃ := K₃
    δ := R / 4
    c_pos := by positivity
    K₁_nonneg := hK₁.le
    K₃_nonneg := hK₃.le
    δ_pos := by positivity
    cutoff_measurable := χ.continuous.measurable
    amplitude_measurable := hameas
    phase_measurable := hpmeas
    model_measurable := hqcont.measurable
    cutoff_nonneg := fun _ => χ.nonneg
    cutoff_le_one := fun _ => χ.le_one
    cutoff_core := fun w hw => χ.one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_zero_right] using hw.le)
    model_im := fun w => (mul_le_mul_of_nonneg_right (by linarith : c / 2 ≤ c)
      (sq_nonneg ‖w‖)).trans (hq w)
    phase_im := fun w hw => by
      rw [(hext w hw).2]
      exact hpositive w ((hsupport w hw).trans_le hRs)
    amplitude_error := fun w hw => by
      rw [(hext w hw).1]
      exact hamp w ((hsupport w hw).trans_le hRr)
    phase_error := fun w hw => by
      rw [(hext w hw).2]
      exact hphase w ((hsupport w hw).trans_le hRr) }
  refine ⟨D, χ.hasCompactSupport, rfl, rfl, hext, ?_, χ.contDiff,
    fun w hw => (hsupport w hw).trans_le hRr⟩
  intro w hw
  change ‖pext w‖ ≤ ρ / 2
  rw [(hext w hw).2]
  exact (hsmallBall (by simpa only [dist_zero_right] using (hsupport w hw).trans_le hRt)).le

theorem continuous_realTransverse : Continuous realTransverse := by
  unfold realTransverse
  fun_prop

theorem eventually_continuousAt_realTransverse {a : ℂ × ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) :
    ∀ᶠ w in 𝓝 (0 : ℂ), ContinuousAt (fun w => a (realTransverse w)) w := by
  have ht : Tendsto realTransverse (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ × ℂ)) := by
    simpa only [realTransverse, zero_re, zero_im, ofReal_zero, Prod.mk_zero_zero] using
      continuous_realTransverse.continuousAt.tendsto (x := (0 : ℂ))
  filter_upwards [ht.eventually ha.eventually_analyticAt] with w hw
  exact hw.continuousAt.comp continuous_realTransverse.continuousAt

/-- The analytic implicit root and residue amplitude supply all Taylor,
positivity, measurability, compact-cutoff and small-pole conditions used by
the actual Fourier residue and Gaussian estimates. -/
theorem exists_localSaddleData_of_analytic_pole_within
    {F : (ℂ × ℂ) × ℂ → ℂ} {a p : ℂ × ℂ → ℂ}
    (hF : AnalyticAt ℂ F (0, 0)) (ha : AnalyticAt ℂ a 0) (hp : AnalyticAt ℂ p 0)
    (hp₀ : p 0 = 0) (hp₁ : fderiv ℂ p 0 = 0)
    (hroot : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), F (w, p w) = 0)
    (hu : (fderiv ℂ F (0, 0)) (0, 1) ≠ 0)
    {ρ v q₁ q₂ ε : ℝ} (hρ : 0 < ρ) (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hε : 0 < ε)
    (hquadratic : ∀ w : ℂ,
      -(2 : ℂ)⁻¹ * ((fderiv ℂ F (0, 0)) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ F) (0, 0)) (realTransverse w, 0) (realTransverse w, 0) =
          quadraticPhase v q₁ q₂ w) :
    ∃ S : LocalSaddleData, HasCompactSupport S.cutoff ∧
      S.model = quadraticPhase v q₁ q₂ ∧ S.amplitude0 = a 0 ∧
      (∀ w, S.cutoff w ≠ 0 → S.amplitude w = a (realTransverse w) ∧
        S.phase w = p (realTransverse w)) ∧
      (∀ w, S.cutoff w ≠ 0 → ‖S.phase w‖ ≤ ρ / 2) ∧
      ContDiff ℝ ∞ S.cutoff ∧ (∀ w, S.cutoff w ≠ 0 → ‖w‖ < ε) := by
  obtain ⟨K₁, hK₁, δ₁, hδ₁, hamp⟩ := analytic_amplitude_bound ha
  obtain ⟨K₃, hK₃, δ₃, hδ₃, hphase⟩ :=
    implicit_phase_cubic_remainder hF hp hp₀ hp₁ hroot hu
  obtain ⟨t, ht, hcont⟩ := Metric.eventually_nhds_iff.mp
    ((eventually_continuousAt_realTransverse ha).and (eventually_continuousAt_realTransverse hp))
  let r := min δ₁ (min δ₃ (min t ε))
  have hr : 0 < r := lt_min hδ₁ (lt_min hδ₃ (lt_min ht hε))
  have hr₁ : r ≤ δ₁ := min_le_left _ _
  have hr₃ : r ≤ δ₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hrt : r ≤ t := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrε : r ≤ ε := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have ha' : ContinuousOn (fun w => a (realTransverse w)) (ball 0 r) := by
    intro w hw
    exact (hcont ((mem_ball.mp hw).trans_le hrt)).1.continuousWithinAt
  have hp' : ContinuousOn (fun w => p (realTransverse w)) (ball 0 r) := by
    intro w hw
    exact (hcont ((mem_ball.mp hw).trans_le hrt)).2.continuousWithinAt
  have hz : realTransverse 0 = 0 := by simp [realTransverse]
  have hamp' (w : ℂ) (hw : ‖w‖ < r) :
      ‖a (realTransverse w) - a (realTransverse 0)‖ ≤ K₁ * ‖w‖ := by
    rw [hz]
    exact (hamp _ ((norm_realTransverse_le w).trans_lt (hw.trans_le hr₁))).trans
      (mul_le_mul_of_nonneg_left (norm_realTransverse_le w) hK₁.le)
  have hphase' (w : ℂ) (hw : ‖w‖ < r) :
      ‖p (realTransverse w) - quadraticPhase v q₁ q₂ w‖ ≤ K₃ * ‖w‖ ^ 3 := by
    have h := hphase (realTransverse w)
      ((norm_realTransverse_le w).trans_lt (hw.trans_le hr₃))
    rw [hquadratic w] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_realTransverse_le w) 3) hK₃.le)
  obtain ⟨S, hs, hm, ha₀, heq, hsmall, hc, hsupport⟩ :=
    exists_localSaddleData_of_local_estimates_with_support
    (fun w => a (realTransverse w)) (fun w => p (realTransverse w)) hr hρ hv hq₁ hq₂
    hK₁ hK₃ ha' hp' (by simpa only [hz] using hp₀) hamp' hphase'
  exact ⟨S, hs, hm, by simpa only [hz] using ha₀, heq, hsmall, hc,
    fun w hw => (hsupport w hw).trans_le hrε⟩

theorem exists_localSaddleData_of_analytic_pole
    {F : (ℂ × ℂ) × ℂ → ℂ} {a p : ℂ × ℂ → ℂ}
    (hF : AnalyticAt ℂ F (0, 0)) (ha : AnalyticAt ℂ a 0) (hp : AnalyticAt ℂ p 0)
    (hp₀ : p 0 = 0) (hp₁ : fderiv ℂ p 0 = 0)
    (hroot : ∀ᶠ w in 𝓝 (0 : ℂ × ℂ), F (w, p w) = 0)
    (hu : (fderiv ℂ F (0, 0)) (0, 1) ≠ 0)
    {ρ v q₁ q₂ : ℝ} (hρ : 0 < ρ) (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hquadratic : ∀ w : ℂ,
      -(2 : ℂ)⁻¹ * ((fderiv ℂ F (0, 0)) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ F) (0, 0)) (realTransverse w, 0) (realTransverse w, 0) =
          quadraticPhase v q₁ q₂ w) :
    ∃ S : LocalSaddleData, HasCompactSupport S.cutoff ∧
      S.model = quadraticPhase v q₁ q₂ ∧ S.amplitude0 = a 0 ∧
      (∀ w, S.cutoff w ≠ 0 → S.amplitude w = a (realTransverse w) ∧
        S.phase w = p (realTransverse w)) ∧
      (∀ w, S.cutoff w ≠ 0 → ‖S.phase w‖ ≤ ρ / 2) := by
  obtain ⟨S, hs, hm, ha₀, heq, hsmall, _, _⟩ :=
    exists_localSaddleData_of_analytic_pole_within hF ha hp hp₀ hp₁ hroot hu
      hρ hv hq₁ hq₂ zero_lt_one hquadratic
  exact ⟨S, hs, hm, ha₀, heq, hsmall⟩

/-- Complete local saddle construction from an analytic numerator and a
simple denominator. The root and its Taylor estimates are constructed;
the only quadratic input is the actual denominator Hessian in transverse
principal coordinates. -/
theorem exists_saddle_data_from_simple_denominator
    (A F : (ℂ × ℂ) × ℂ → ℂ)
    (hA : AnalyticAt ℂ A (0, 0)) (hF : AnalyticAt ℂ F (0, 0)) (hF₀ : F (0, 0) = 0)
    (hu : (fderiv ℂ F (0, 0)) (0, 1) ≠ 0)
    (htrans : (fderiv ℂ F (0, 0)).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) = 0)
    {ρ v q₁ q₂ : ℝ} (hρ : 0 < ρ) (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hquadratic : ∀ w : ℂ,
      -(2 : ℂ)⁻¹ * ((fderiv ℂ F (0, 0)) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ F) (0, 0)) (realTransverse w, 0) (realTransverse w, 0) =
          quadraticPhase v q₁ q₂ w) :
    ∃ (p : ℂ × ℂ → ℂ) (S : LocalSaddleData),
      p 0 = 0 ∧ AnalyticAt ℂ p 0 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ × ℂ), F (w, p w) = 0) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : (ℂ × ℂ) × ℂ), F z = 0 ↔ p z.1 = z.2) ∧
      HasCompactSupport S.cutoff ∧ S.model = quadraticPhase v q₁ q₂ ∧
      S.amplitude0 = A (0, 0) / (fderiv ℂ F (0, 0)) (0, 1) ∧
      (∀ w, S.cutoff w ≠ 0 →
        S.amplitude w = A (realTransverse w, p (realTransverse w)) /
          (fderiv ℂ F (realTransverse w, p (realTransverse w))) (0, 1) ∧
        S.phase w = p (realTransverse w)) ∧
      (∀ w, S.cutoff w ≠ 0 → ‖S.phase w‖ ≤ ρ / 2) := by
  obtain ⟨p, hp₀, hp, hp₁, hroot, huniq, _⟩ :=
    exists_analytic_stationary_pole F hF hF₀ hu htrans
  have ha := analytic_residue_amplitude hA hF hp hp₀ hu
  obtain ⟨S, hs, hmodel, ha₀, heq, hsmall⟩ :=
    exists_localSaddleData_of_analytic_pole hF ha hp hp₀ hp₁ hroot hu
      hρ hv hq₁ hq₂ hquadratic
  exact ⟨p, S, hp₀, hp, hroot, huniq, hs, hmodel,
    by simpa only [hp₀] using ha₀, heq, hsmall⟩

end Maxwell.Green
