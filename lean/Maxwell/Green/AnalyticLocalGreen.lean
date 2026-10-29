import Maxwell.Green.SaddleConstruction
import Maxwell.Green.NormalDisk
import Maxwell.Green.LocalAssembly

/-! The local Green integral assembled from an analytic numerator and a
simple stationary denominator. All pole, cutoff, integrability, and
asymptotic data are constructed from the local analytic hypotheses. -/

noncomputable section

namespace Maxwell.Green

open Filter MeasureTheory Complex Metric Set
open scoped Topology ContDiff

def realChartSlice (A : (ℂ × ℂ) × ℂ → ℂ) (w z : ℂ) : ℂ := A (realTransverse w, z)

theorem contDiff_real_normal_slice :
    ContDiff ℝ ∞ (fun x : ℂ × ℝ => (realTransverse x.1, (x.2 : ℂ))) := by
  exact ((ofRealCLM.contDiff.comp (reCLM.contDiff.comp contDiff_fst)).prodMk
    (ofRealCLM.contDiff.comp (imCLM.contDiff.comp contDiff_fst))).prodMk
    (ofRealCLM.contDiff.comp contDiff_snd)

/-- The localization data needed to identify the original quotient and to
glue its regular part into the full torus integral. -/
structure AnalyticLocalGreenData (A F : (ℂ × ℂ) × ℂ → ℂ) (v q₁ q₂ : ℝ) where
  transverseRadius : ℝ
  transverseRadius_pos : 0 < transverseRadius
  normalRadius : ℝ
  normalRadius_pos : 0 < normalRadius
  cutoffRadius : ℝ
  cutoffRadius_pos : 0 < cutoffRadius
  cutoffRadius_le : 4 * cutoffRadius ≤ normalRadius
  pole : ℂ × ℂ → ℂ
  pole_zero : pole 0 = 0
  pole_analytic : AnalyticAt ℂ pole 0
  pole_im_positive : ∀ w : ℂ, ‖w‖ ≤ transverseRadius → w ≠ 0 →
    0 < (pole (realTransverse w)).im
  normalData : ∀ w, ‖w‖ ≤ transverseRadius →
    ‖pole w‖ < normalRadius / 2 ∧
    (∀ u ∈ closedBall (0 : ℂ) normalRadius, AnalyticAt ℂ A (w, u) ∧ AnalyticAt ℂ F (w, u)) ∧
    AnalyticOnNhd ℂ (fun u => A (w, u)) (closedBall 0 normalRadius) ∧
    AnalyticOnNhd ℂ (fun u => F (w, u)) (closedBall 0 normalRadius) ∧
    F (w, pole w) = 0 ∧ deriv (fun u => F (w, u)) (pole w) ≠ 0 ∧
    (∀ u ∈ closedBall (0 : ℂ) normalRadius, F (w, u) = 0 → u = pole w)
  saddle : LocalSaddleData
  regular : RegularNormalData
  cutoff_compact : HasCompactSupport saddle.cutoff
  cutoff_smooth : ContDiff ℝ ∞ saddle.cutoff
  model_eq : saddle.model = quadraticPhase v q₁ q₂
  amplitude_zero : saddle.amplitude0 = A (0, 0) / (fderiv ℂ F (0, 0)) (0, 1)
  support_bound : ∀ w, saddle.cutoff w ≠ 0 → ‖w‖ < transverseRadius
  phase_eq : ∀ w, saddle.cutoff w ≠ 0 → saddle.phase w = pole (realTransverse w)
  phase_bound : ∀ w, saddle.cutoff w ≠ 0 → ‖saddle.phase w‖ ≤ cutoffRadius / 2
  amplitude_eq : ∀ w, saddle.cutoff w ≠ 0 → saddle.amplitude w =
    realChartSlice A w (saddle.phase w) / deriv (realChartSlice F w) (saddle.phase w)
  regular_eq : ∀ w u, regular.amplitude w u = (saddle.cutoff w : ℂ) *
    (scaledPoleCutoff cutoffRadius u : ℂ) *
      normalCauchyRemainder (realChartSlice A w) (realChartSlice F w) 0 normalRadius u

namespace AnalyticLocalGreenData

variable {A F : (ℂ × ℂ) × ℂ → ℂ} {v q₁ q₂ : ℝ}
variable (D : AnalyticLocalGreenData A F v q₁ q₂)

def normalCutoffRadius : ℝ := D.cutoffRadius

theorem normalCutoffRadius_pos : 0 < D.normalCutoffRadius := D.cutoffRadius_pos

theorem support_realTransverse {w : ℂ} (hw : D.saddle.cutoff w ≠ 0) :
    ‖realTransverse w‖ ≤ D.transverseRadius :=
  (norm_realTransverse_le w).trans (D.support_bound w hw).le

/-- The actual denominator has no additional real zeros throughout the
closed local chart, including the boundary of the cutoff support. -/
theorem denominator_ne_zero {w : ℂ} {u : ℝ}
    (hw : ‖w‖ ≤ D.transverseRadius) (hu : |u| ≤ D.normalRadius)
    (hpair : (w, u) ≠ (0, 0)) : realChartSlice F w u ≠ 0 := by
  intro hzero
  have he := (D.normalData (realTransverse w) ((norm_realTransverse_le w).trans hw)).2.2.2.2.2.2
    (u : ℂ) (by simpa only [mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs]
      using hu) hzero
  by_cases hw₀ : w = 0
  · have hu₀ : u = 0 := by
      simpa only [hw₀, realTransverse, zero_re, zero_im, ofReal_zero,
        Prod.mk_zero_zero, D.pole_zero, ofReal_eq_zero] using he
    exact hpair (by simp only [hw₀, hu₀])
  · have him := D.pole_im_positive w hw hw₀
    rw [← he] at him
    simp only [ofReal_im, lt_self_iff_false] at him

/-- Joint smoothness of the original quotient on the punctured real chart. -/
theorem quotient_contDiffAt {w : ℂ} {u : ℝ}
    (hw : ‖w‖ ≤ D.transverseRadius) (hu : |u| ≤ D.normalRadius)
    (hpair : (w, u) ≠ (0, 0)) :
    ContDiffAt ℝ ∞ (fun x : ℂ × ℝ => realChartSlice A x.1 x.2 /
      realChartSlice F x.1 x.2) (w, u) := by
  have hj := (D.normalData (realTransverse w) ((norm_realTransverse_le w).trans hw)).2.1
    (u : ℂ) (by simpa only [mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs]
      using hu)
  have hquot : AnalyticAt ℂ (fun z => A z / F z) (realTransverse w, (u : ℂ)) :=
    hj.1.div hj.2 (D.denominator_ne_zero hw hu hpair)
  exact hquot.restrictScalars.contDiffAt.comp (w, u) contDiff_real_normal_slice.contDiffAt

/-- Exact equality with the original localized numerator/denominator
integral, obtained from the fixed-circle simple-pole formula. -/
theorem localizedQuotientIntegral_eq {T : ℝ} (hT : 0 < T) :
    localizedQuotientIntegral D.saddle (realChartSlice A) (realChartSlice F)
      D.normalCutoffRadius T = localGreenIntegral D.saddle D.regular D.normalCutoffRadius T := by
  apply Maxwell.Green.localizedQuotientIntegral_eq D.saddle D.regular
    (realChartSlice A) (realChartSlice F) D.normalCutoffRadius_pos
    D.cutoffRadius_le
    D.cutoff_compact D.phase_bound
  · intro w hw
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.1
  · intro w hw
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.2.1
  · intro w hw
    rw [realChartSlice, D.phase_eq w hw]
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.2.2.1
  · intro w hw
    rw [D.phase_eq w hw]
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.2.2.2.1
  · intro w hw u hu hz
    rw [D.phase_eq w hw]
    exact (D.normalData _ (D.support_realTransverse hw)).2.2.2.2.2.2 u hu hz
  · exact D.amplitude_eq
  · exact D.regular_eq
  · exact hT

/-- The original localized analytic quotient has the actual residue and
transverse determinant coefficient, with an inverse-three-halves error. -/
theorem localizedQuotientIntegral_asymptotic (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ‖localizedQuotientIntegral D.saddle (realChartSlice A) (realChartSlice F)
          D.normalCutoffRadius T -
        (2 * Real.pi : ℂ) * I * ((A (0, 0) / (fderiv ℂ F (0, 0)) (0, 1)) *
          ((2 * Real.pi * v / (T * Real.sqrt (q₁ * q₂)) : ℝ) : ℂ))‖ ≤
        C * T ^ (-(3 : ℝ) / 2) := by
  obtain ⟨C, hC, hb⟩ := localGreenIntegral_asymptotic D.saddle D.regular
    D.normalCutoffRadius_pos D.cutoff_compact D.phase_bound hv hq₁ hq₂ D.model_eq
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with T h hT
  rw [D.localizedQuotientIntegral_eq hT]
  simpa only [D.amplitude_zero] using h

end AnalyticLocalGreenData

/-- An analytic numerator and a simple stationary denominator construct all
local Green data. Global measurability is not required: only the original
quotient on a compact transverse ball times the fixed circle is extended. -/
theorem exists_analyticLocalGreenData_within
    (A F : (ℂ × ℂ) × ℂ → ℂ)
    (hA : AnalyticAt ℂ A (0, 0)) (hF : AnalyticAt ℂ F (0, 0)) (hF₀ : F (0, 0) = 0)
    (hu : (fderiv ℂ F (0, 0)) (0, 1) ≠ 0)
    (htrans : (fderiv ℂ F (0, 0)).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) = 0)
    {v q₁ q₂ η : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hη : 0 < η)
    (hquadratic : ∀ w : ℂ,
      -(2 : ℂ)⁻¹ * ((fderiv ℂ F (0, 0)) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ F) (0, 0)) (realTransverse w, 0) (realTransverse w, 0) =
          quadraticPhase v q₁ q₂ w) :
    ∃ D : AnalyticLocalGreenData A F v q₁ q₂,
      D.normalCutoffRadius ≤ η ∧
      tsupport D.saddle.cutoff ⊆ ball (0 : ℂ) D.transverseRadius ∧
      tsupport D.saddle.cutoff ⊆ ball (0 : ℂ) η := by
  classical
  obtain ⟨p, hp₀, hp, hp₁, hroot, huniq, K₃, hK₃, δ₃, hδ₃, hphase⟩ :=
    exists_analytic_stationary_pole F hF hF₀ hu htrans
  obtain ⟨r₀, hr₀, R, hR, hnormal₀⟩ :=
    exists_uniform_normal_disk A F p hA hF hp.continuousAt hp₀ hu huniq
  let c : ℝ := min q₁ q₂ / (2 * v)
  have hc : 0 < c := div_pos (lt_min hq₁ hq₂) (by positivity)
  have hphase' (w : ℂ) (hw : ‖w‖ < δ₃) :
      ‖p (realTransverse w) - quadraticPhase v q₁ q₂ w‖ ≤ K₃ * ‖w‖ ^ 3 := by
    have h := hphase (realTransverse w) ((norm_realTransverse_le w).trans_lt hw)
    rw [hquadratic w] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_realTransverse_le w) 3) hK₃.le)
  have hq (w : ℂ) : c * ‖w‖ ^ 2 ≤ (quadraticPhase v q₁ q₂ w).im := by
    apply quadraticPhase_im_lower hv
    · dsimp [c]
      rw [mul_div_cancel₀ _ (by positivity : 2 * v ≠ 0)]
      exact min_le_left _ _
    · dsimp [c]
      rw [mul_div_cancel₀ _ (by positivity : 2 * v ≠ 0)]
      exact min_le_right _ _
  obtain ⟨s, hspos, hpositive⟩ := cubic_perturbation_has_positive_imaginary_part
    hK₃ hδ₃ hc hphase' hq
  let r := min r₀ (s / 2)
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hnormal (w : ℂ × ℂ) (hw : ‖w‖ ≤ r) :=
    hnormal₀ w (hw.trans (min_le_left _ _))
  have hpim (w : ℂ) (hw : ‖w‖ ≤ r) (hw₀ : w ≠ 0) :
      0 < (p (realTransverse w)).im := by
    have hws : ‖w‖ < s := lt_of_le_of_lt
      (hw.trans (min_le_right _ _)) (by linarith)
    exact lt_of_lt_of_le (mul_pos (by positivity : 0 < c / 2)
      (sq_pos_of_pos (norm_pos_iff.mpr hw₀))) (hpositive w hws)
  let ρ := min (R / 8) η
  have hρ : 0 < ρ := lt_min (by positivity) hη
  have hρR : 4 * ρ ≤ R := by have := min_le_left (R / 8) η; dsimp [ρ]; linarith
  let ε := min (r / 2) (η / 2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have ha := analytic_residue_amplitude hA hF hp hp₀ hu
  obtain ⟨S, hs, hm, ha₀, heq, hsmall, hsc, hsupport⟩ :=
    exists_localSaddleData_of_analytic_pole_within hF ha hp hp₀ hp₁ hroot hu
      hρ hv hq₁ hq₂ hε hquadratic
  have hsε : tsupport S.cutoff ⊆ closedBall (0 : ℂ) ε := by
    apply closure_minimal _ isClosed_closedBall
    intro w hw
    exact mem_closedBall.mpr (by simpa only [dist_zero_right] using (hsupport w hw).le)
  have hsr (w : ℂ) (hw : w ∈ tsupport S.cutoff) : ‖w‖ < r := by
    have hn : ‖w‖ ≤ ε := by simpa only [mem_closedBall, dist_zero_right] using hsε hw
    exact lt_of_le_of_lt (hn.trans (min_le_left _ _)) (by linarith)
  have hsη (w : ℂ) (hw : w ∈ tsupport S.cutoff) : ‖w‖ < η := by
    have hn : ‖w‖ ≤ ε := by simpa only [mem_closedBall, dist_zero_right] using hsε hw
    exact lt_of_le_of_lt (hn.trans (min_le_right _ _)) (by linarith)
  have hparameter (w : ℂ) (hw : S.cutoff w ≠ 0) : ‖realTransverse w‖ ≤ r :=
    (norm_realTransverse_le w).trans (hsr w (subset_closure hw)).le
  have hboundary (w : ℂ × ℂ) (hw : ‖w‖ ≤ r) :
      ∀ z ∈ sphere (0 : ℂ) R, F (w, z) ≠ 0 :=
    normal_disk_boundary_nonzero hR (hnormal w hw).1 (hnormal w hw).2.2.2.2.2.2
  obtain ⟨M, hM, hbound⟩ := exists_uniform_circle_quotient_bound A F r R
    (fun w hw z hz => ((hnormal w (by simpa only [mem_closedBall, dist_zero_right] using hw)).2.1
      z (sphere_subset_closedBall hz)).1)
    (fun w hw z hz => ((hnormal w (by simpa only [mem_closedBall, dist_zero_right] using hw)).2.1
      z (sphere_subset_closedBall hz)).2)
    (fun w hw => hboundary w (by simpa only [mem_closedBall, dist_zero_right] using hw))
  let K := closedBall (0 : ℂ × ℂ) r ×ˢ sphere (0 : ℂ) R
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ × ℂ) r).prod (isCompact_sphere (0 : ℂ) R)
  have hQ : ContinuousOn (fun z : (ℂ × ℂ) × ℂ => A z / F z) K := by
    intro z hz
    have hw : ‖z.1‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz.1
    have hj := (hnormal z.1 hw).2.1 z.2 (sphere_subset_closedBall hz.2)
    exact (hj.1.continuousAt.div hj.2.continuousAt (hboundary z.1 hw z.2 hz.2)).continuousWithinAt
  let Q : (ℂ × ℂ) × ℂ → ℂ := K.piecewise (fun z => A z / F z) (fun _ => 0)
  have hQm : Measurable Q := hQ.measurable_piecewise continuousOn_const hK.measurableSet
  let f : ℂ → ℂ → ℂ := fun w z => Q (realTransverse w, z)
  have hfm : Measurable (Function.uncurry f) := hQm.comp
    ((continuous_realTransverse.measurable.comp measurable_fst).prodMk measurable_snd)
  have hfeq (w : ℂ) (hw : S.cutoff w ≠ 0) (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
      f w z = realChartSlice A w z / realChartSlice F w z := by
    apply piecewise_eq_of_mem
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hparameter w hw, hz⟩
  have hfb (w : ℂ) (hw : (S.cutoff w : ℂ) ≠ 0) (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
      ‖f w z‖ ≤ M := by
    have hw' : S.cutoff w ≠ 0 := Complex.ofReal_ne_zero.mp hw
    rw [hfeq w hw' z hz]
    exact hbound _ (by simpa only [mem_closedBall, dist_zero_right] using hparameter w hw') z hz
  obtain ⟨D, hD⟩ := exists_scaled_cauchyRegularData (fun w => (S.cutoff w : ℂ)) f
    (Complex.continuous_ofReal.comp hsc.continuous) (hs.comp_left Complex.ofReal_zero)
    hfm hρ hR hρR hM hfb
  have hregular (w : ℂ) (u : ℝ) : D.amplitude w u = (S.cutoff w : ℂ) *
      (scaledPoleCutoff ρ u : ℂ) *
        normalCauchyRemainder (realChartSlice A w) (realChartSlice F w) 0 R u := by
    rw [hD, cutoffCauchy]
    by_cases hw : S.cutoff w = 0
    · simp only [hw, Complex.ofReal_zero, zero_mul]
    have he : cauchyTerm (f w) 0 0 R u =
        normalCauchyRemainder (realChartSlice A w) (realChartSlice F w) 0 R u := by
      unfold cauchyTerm normalCauchyRemainder
      simp only [Nat.zero_add, Nat.cast_one, zpow_neg_one]
      congr 1
      apply circleIntegral.integral_congr hR.le
      intro z hz
      exact congrArg ((z - (u : ℂ))⁻¹ * ·) (hfeq w hw z hz)
    rw [he]
    ring
  refine ⟨{
    transverseRadius := r
    transverseRadius_pos := hr
    normalRadius := R
    normalRadius_pos := hR
    cutoffRadius := ρ
    cutoffRadius_pos := hρ
    cutoffRadius_le := hρR
    pole := p
    pole_zero := hp₀
    pole_analytic := hp
    pole_im_positive := hpim
    normalData := hnormal
    saddle := S
    regular := D
    cutoff_compact := hs
    cutoff_smooth := hsc
    model_eq := hm
    amplitude_zero := by simpa only [hp₀] using ha₀
    support_bound := fun w hw => hsr w (subset_closure hw)
    phase_eq := fun w hw => (heq w hw).2
    phase_bound := hsmall
    amplitude_eq := ?_
    regular_eq := hregular
  }, min_le_right _ _, (fun w hw => mem_ball.mpr (by simpa only [dist_zero_right] using hsr w hw)),
    (fun w hw => mem_ball.mpr (by simpa only [dist_zero_right] using hsη w hw))⟩
  intro w hw
  rw [(heq w hw).1, (heq w hw).2]
  have hn := hnormal (realTransverse w) (hparameter w hw)
  have hpR : p (realTransverse w) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right]
    exact hn.1.le.trans (by linarith)
  unfold realChartSlice
  rw [deriv_normal_slice (hn.2.1 _ hpR).2]

theorem exists_analyticLocalGreenData
    (A F : (ℂ × ℂ) × ℂ → ℂ)
    (hA : AnalyticAt ℂ A (0, 0)) (hF : AnalyticAt ℂ F (0, 0)) (hF₀ : F (0, 0) = 0)
    (hu : (fderiv ℂ F (0, 0)) (0, 1) ≠ 0)
    (htrans : (fderiv ℂ F (0, 0)).comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) = 0)
    {v q₁ q₂ : ℝ} (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hquadratic : ∀ w : ℂ,
      -(2 : ℂ)⁻¹ * ((fderiv ℂ F (0, 0)) (0, 1))⁻¹ *
        (fderiv ℂ (fderiv ℂ F) (0, 0)) (realTransverse w, 0) (realTransverse w, 0) =
          quadraticPhase v q₁ q₂ w) :
    Nonempty (AnalyticLocalGreenData A F v q₁ q₂) := by
  obtain ⟨D, _⟩ := exists_analyticLocalGreenData_within A F hA hF hF₀ hu htrans
    hv hq₁ hq₂ zero_lt_one hquadratic
  exact ⟨D⟩

end Maxwell.Green
