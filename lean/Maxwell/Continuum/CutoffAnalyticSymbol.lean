import Maxwell.Continuum.SeparatedSymbolCutoff

/-! Operator-valued analytic symbols retain explicit Gevrey estimates
after multiplication by the literal compact momentum cutoff. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber OperatorFourier PeriodicBand Set Metric Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  (f : Momentum → F) {C : ℝ}

def realSymbol (q : Space) : F := f (realMomentumMap q)
def cutoffSymbol (q : Space) : F := (cutoff q : ℂ) • realSymbol f q

theorem cutoffSymbol_tsupport : tsupport (cutoffSymbol f) ⊆ closedBall (0 : Space) (4 * smallRadius) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  have hc : cutoff q ≠ 0 := by
    intro he
    apply (Function.mem_support.mp hq)
    rw [cutoffSymbol, he, Complex.ofReal_zero]
    exact zero_smul ℂ (realSymbol f q)
  simpa only [mem_closedBall, dist_zero_right] using cutoff_ne_zero_norm_le hc

theorem cutoffSymbol_compact : HasCompactSupport (cutoffSymbol f) :=
  (isCompact_closedBall (0 : Space) (4 * smallRadius)).of_isClosed_subset isClosed_closure
    (cutoffSymbol_tsupport f)

variable [CompleteSpace F]

theorem analyticSymbol_line_derivative
    (hf : AnalyticOnNhd ℂ f (closedBall 0 separatedRadius))
    (hb : ∀ q ∈ closedBall 0 separatedRadius, ‖f q‖ ≤ C) (hC : 0 ≤ C)
    {q v : Momentum} (hq : ‖q‖ ≤ separatedRadius / 2) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖iteratedDeriv K (fun s : ℝ => f (q + (s : ℂ) • v)) 0‖ ≤
      C * ((2 : ℝ)^156)^K * (K.factorial : ℝ)^2 := by
  let g : ℂ → F := fun s => f (q + s • v)
  have ha : AnalyticOnNhd ℂ g (closedBall 0 (separatedRadius / 2)) := by
    intro s hs
    exact (hf _ (separated_line_mem hq hv hs)).comp
      (f := fun s : ℂ => q + s • v) (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hc : ∀ s ∈ closedBall (0 : ℂ) (separatedRadius / 2), ‖g s‖ ≤ C := by
    intro s hs
    exact hb _ (separated_line_mem hq hv hs)
  change ‖iteratedDeriv K (fun s : ℝ => g s) 0‖ ≤ _
  rw [OperatorFourier.iteratedDeriv_restrict_complex g (ball 0 (separatedRadius / 2))
    isOpen_ball (ha.mono ball_subset_closedBall) K 0 (by simpa using half_pos separatedRadius_pos)]
  have hd := CauchyBounds.norm_iteratedDeriv_le K ha hc
    (half_pos separatedRadius_pos) (c := 0) (by simp)
  have hr : (separatedRadius / 2)⁻¹ ≤ (2 : ℝ)^156 := by
    norm_num [separatedRadius, backgroundAmplitude]
  have hfac : (K.factorial : ℝ) ≤ (K.factorial : ℝ)^2 := by
    have hp : (1 : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_pos K
    nlinarith
  have hr0 : 0 ≤ (separatedRadius / 2)⁻¹ := (inv_pos.mpr (half_pos separatedRadius_pos)).le
  calc
    _ ≤ K.factorial * C / (separatedRadius / 2)^K := hd
    _ = C * ((separatedRadius / 2)⁻¹)^K * K.factorial := by
      rw [div_eq_mul_inv, ← inv_pow]
      ring
    _ ≤ _ := by gcongr

theorem realSymbol_contDiffAt
    (hf : AnalyticOnNhd ℂ f (closedBall 0 separatedRadius))
    {q : Space} (hq : ‖q‖ ≤ separatedRadius) :
    ContDiffAt ℝ (⊤ : ℕ∞) (realSymbol f) q := by
  have hm : realMomentumMap q ∈ closedBall 0 separatedRadius := by
    simpa using (realMomentumMap_norm_le q).trans hq
  exact ((hf _ hm).contDiffAt.restrict_scalars ℝ).comp q realMomentumMap.contDiff.contDiffAt

theorem realSymbol_line_derivative
    (hf : AnalyticOnNhd ℂ f (closedBall 0 separatedRadius))
    (hb : ∀ q ∈ closedBall 0 separatedRadius, ‖f q‖ ≤ C) (hC : 0 ≤ C)
    {q v : Space} (hq : ‖q‖ ≤ separatedRadius / 2) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖iteratedDeriv K (fun s : ℝ => realSymbol f (q + s • v)) 0‖ ≤
      C * ((2 : ℝ)^156)^K * (K.factorial : ℝ)^2 := by
  have he : (fun s : ℝ => realSymbol f (q + s • v)) =
      (fun s : ℝ => f (realMomentumMap q + (s : ℂ) • realMomentumMap v)) := by
    funext s
    rw [realSymbol, map_add, map_smul]
    rfl
  rw [he]
  exact analyticSymbol_line_derivative f hf hb hC ((realMomentumMap_norm_le q).trans hq)
    ((realMomentumMap_norm_le v).trans hv) K

theorem cutoffSymbol_contDiff
    (hf : AnalyticOnNhd ℂ f (closedBall 0 separatedRadius)) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffSymbol f) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : ‖q‖ ≤ separatedRadius / 2
  · exact (Complex.ofRealCLM.contDiff.comp (Well.chi_contDiff smallRadius)).contDiffAt.smul
      (realSymbol_contDiffAt f hf (hq.trans (by linarith [separatedRadius_pos])))
  · have hq' : 4 * smallRadius < ‖q‖ := lt_of_le_of_lt cutoff_radius_margin (lt_of_not_ge hq)
    have hz : cutoffSymbol f =ᶠ[𝓝 q] (fun _ => 0) := by
      have he : ∀ᶠ p : Space in 𝓝 q, 4 * smallRadius < ‖p‖ :=
        continuous_norm.continuousAt.eventually (eventually_gt_nhds hq')
      filter_upwards [he] with p hp
      have hc : cutoff p = 0 := by
        by_contra hne
        exact (not_lt_of_ge (cutoff_ne_zero_norm_le hne)) hp
      rw [cutoffSymbol, hc, Complex.ofReal_zero]
      exact zero_smul ℂ (realSymbol f p)
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem cutoffSymbol_gevrey
    (hf : AnalyticOnNhd ℂ f (closedBall 0 separatedRadius))
    (hb : ∀ q ∈ closedBall 0 separatedRadius, ‖f q‖ ≤ C) (hC : 0 ≤ C)
    (q v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖directionalDerivative K (cutoffSymbol f) q v‖ ≤
      ((2 : ℝ)^45 * C) * ((2 : ℝ)^157)^K * (K.factorial : ℝ)^2 := by
  by_cases hq : ‖q‖ ≤ separatedRadius / 2
  · let a : ℝ → ℝ := fun s => cutoff (q + s • v)
    let b : ℝ → F := fun s => realSymbol f (q + s • v)
    have ha : ContDiff ℝ (⊤ : ℕ∞) a := (Well.chi_contDiff smallRadius).comp (by fun_prop)
    have hb' : ContDiffAt ℝ (⊤ : ℕ∞) b 0 := by
      have hat : ContDiffAt ℝ (⊤ : ℕ∞) (realSymbol f) (q + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using realSymbol_contDiffAt f hf
          (hq.trans (by linarith [separatedRadius_pos]))
      simpa only [Function.comp_def] using hat.comp 0
        (show ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => q + s • v) 0 by fun_prop)
    have hab (n : ℕ) : |iteratedDeriv n a 0| ≤
        (2 : ℝ)^45 * ((2 : ℝ)^156)^n * (n.factorial : ℝ)^2 := by
      have hd := Well.chi_directional_gevrey smallRadius smallRadius_pos q v hv n
      rw [Well.directionalDerivative_eq_line n (Well.chi smallRadius)
        (Well.chi_contDiff smallRadius)] at hd
      have hc : (2 : ℝ)^16 / smallRadius = (2 : ℝ)^156 := by
        norm_num [smallRadius, backgroundAmplitude]
      rw [hc] at hd
      exact hd
    have hbb (n : ℕ) : ‖iteratedDeriv n b 0‖ ≤
        C * ((2 : ℝ)^156)^n * (n.factorial : ℝ)^2 :=
      realSymbol_line_derivative f hf hb hC hq hv n
    have hd := gevrey_smul a b 0 ha.contDiffAt hb' (2^45) C (2^156)
      (by positivity) hC (by positivity) hab hbb K
    rw [directionalDerivative_eq_line K (cutoffSymbol f) (cutoffSymbol_contDiff f hf)]
    have he : (fun s : ℝ => cutoffSymbol f (q + s • v)) = (fun s => a s • b s) := rfl
    rw [he]
    have hc : (2 : ℝ) * 2^156 = 2^157 := by norm_num
    rw [hc] at hd
    exact hd
  · have hz : iteratedFDeriv ℝ K (cutoffSymbol f) q = 0 := by
      apply Function.notMem_support.mp
      intro hm
      have hs := cutoffSymbol_tsupport f (support_iteratedFDeriv_subset K hm)
      have hs' : ‖q‖ ≤ 4 * smallRadius := by simpa using hs
      exact hq (hs'.trans cutoff_radius_margin)
    unfold directionalDerivative
    rw [hz]
    simp only [zero_apply, norm_zero]
    positivity

theorem cutoffSymbol_fourier_decay
    (hf : AnalyticOnNhd ℂ f (closedBall 0 separatedRadius))
    (hb : ∀ q ∈ closedBall 0 separatedRadius, ‖f q‖ ≤ C) (hC : 0 < C) (p : Space) :
    ‖angularFourier (cutoffSymbol f) p‖ ≤
      24 * ((2 : ℝ)^45 * C) * Real.exp (-Real.sqrt (400 * ‖p‖ / (2 : ℝ)^157) / 64) := by
  apply angularFourier_gevrey_decay (cutoffSymbol f) (cutoffSymbol_contDiff f hf)
    (cutoffSymbol_compact f) ((cutoffSymbol_tsupport f).trans
      (closedBall_subset_closedBall (by norm_num [smallRadius, backgroundAmplitude])))
    (by positivity) (by positivity)
  intro K q v hv
  exact cutoffSymbol_gevrey f hf hb hC.le q v hv K

#print axioms cutoffSymbol_gevrey
#print axioms cutoffSymbol_fourier_decay

end Maxwell.Continuum.Auxiliary
