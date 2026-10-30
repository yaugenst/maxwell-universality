import Maxwell.Continuum.CutoffAnalyticSymbol

/-! A local version of cutoff Gevrey estimates. Smoothness and derivative
bounds are needed only near the actual cutoff support, allowing poles
outside an h-width complex neighborhood. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand OperatorFourier Set Metric Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  (f : Momentum → F)

theorem cutoffSymbol_tsupport_sup : tsupport (cutoffSymbol f) ⊆
    {q | ‖realMomentumMap q‖ ≤ 2 * smallRadius} := by
  apply closure_minimal _ (isClosed_le realMomentumMap.continuous.norm continuous_const)
  intro q hq
  apply cutoff_ne_zero_sup_le
  intro he
  apply (Function.mem_support.mp hq)
  rw [cutoffSymbol, he, Complex.ofReal_zero]
  exact zero_smul ℂ (realSymbol f q)

variable (hf : ∀ q : Space, ‖realMomentumMap q‖ ≤ 3 * smallRadius →
  ContDiffAt ℝ (⊤ : ℕ∞) (realSymbol f) q)

include hf

theorem cutoffSymbol_local_contDiff : ContDiff ℝ (⊤ : ℕ∞) (cutoffSymbol f) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius
  · exact (Complex.ofRealCLM.contDiff.comp (Well.chi_contDiff smallRadius)).contDiffAt.smul (hf q hq)
  · have hq' : 2 * smallRadius < ‖realMomentumMap q‖ := by
      linarith [lt_of_not_ge hq, smallRadius_pos]
    have he : ∀ᶠ p : Space in 𝓝 q, 2 * smallRadius < ‖realMomentumMap p‖ :=
      realMomentumMap.continuous.norm.continuousAt.eventually (eventually_gt_nhds hq')
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [he] with p hp
    have hz : cutoff p = 0 := by
      by_contra hn
      exact (not_lt_of_ge (cutoff_ne_zero_sup_le hn)) hp
    rw [cutoffSymbol, hz, Complex.ofReal_zero]
    exact zero_smul ℂ (realSymbol f p)

theorem cutoffSymbol_local_gevrey {C A : ℝ} (hC : 0 ≤ C) (hA : (2 : ℝ)^156 ≤ A)
    (hd : ∀ (q v : Space), ‖realMomentumMap q‖ ≤ 3 * smallRadius → ‖v‖ ≤ 1 →
      ∀ K : ℕ, ‖iteratedDeriv K (fun s : ℝ => realSymbol f (q + s • v)) 0‖ ≤
        C * A^K * (K.factorial : ℝ)^2)
    (q v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖directionalDerivative K (cutoffSymbol f) q v‖ ≤
      ((2 : ℝ)^45 * C) * (2*A)^K * (K.factorial : ℝ)^2 := by
  have hA0 : 0 ≤ A := (by positivity : (0 : ℝ) ≤ 2^156).trans hA
  by_cases hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius
  · let a : ℝ → ℝ := fun s => cutoff (q + s • v)
    let b : ℝ → F := fun s => realSymbol f (q + s • v)
    have ha : ContDiff ℝ (⊤ : ℕ∞) a := (Well.chi_contDiff smallRadius).comp (by fun_prop)
    have hb : ContDiffAt ℝ (⊤ : ℕ∞) b 0 := by
      have hat : ContDiffAt ℝ (⊤ : ℕ∞) (realSymbol f) (q + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using hf q hq
      simpa only [Function.comp_def] using hat.comp 0
        (show ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => q + s • v) 0 by fun_prop)
    have hab (n : ℕ) : |iteratedDeriv n a 0| ≤ (2 : ℝ)^45 * A^n * (n.factorial : ℝ)^2 := by
      have hcut := Well.chi_directional_gevrey smallRadius smallRadius_pos q v hv n
      rw [Well.directionalDerivative_eq_line n (Well.chi smallRadius)
        (Well.chi_contDiff smallRadius)] at hcut
      have hc : (2 : ℝ)^16 / smallRadius = (2 : ℝ)^156 := by
        norm_num [smallRadius, backgroundAmplitude]
      rw [hc] at hcut
      exact hcut.trans (by gcongr)
    have hbb (n : ℕ) : ‖iteratedDeriv n b 0‖ ≤ C * A^n * (n.factorial : ℝ)^2 := hd q v hq hv n
    have hprod := gevrey_smul a b 0 ha.contDiffAt hb (2^45) C A
      (by positivity) hC hA0 hab hbb K
    rw [directionalDerivative_eq_line K (cutoffSymbol f) (cutoffSymbol_local_contDiff f hf)]
    exact hprod
  · have hz : iteratedFDeriv ℝ K (cutoffSymbol f) q = 0 := by
      apply Function.notMem_support.mp
      intro hm
      have hs := cutoffSymbol_tsupport_sup f (support_iteratedFDeriv_subset K hm)
      exact hq (hs.trans (by linarith [smallRadius_pos]))
    unfold directionalDerivative
    rw [hz]
    simp only [zero_apply, norm_zero]
    positivity

theorem cutoffSymbol_local_fourier_decay [CompleteSpace F] {C A : ℝ}
    (hC : 0 < C) (hA : (2 : ℝ)^156 ≤ A)
    (hd : ∀ (q v : Space), ‖realMomentumMap q‖ ≤ 3 * smallRadius → ‖v‖ ≤ 1 →
      ∀ K : ℕ, ‖iteratedDeriv K (fun s : ℝ => realSymbol f (q + s • v)) 0‖ ≤
        C * A^K * (K.factorial : ℝ)^2) (p : Space) :
    ‖angularFourier (cutoffSymbol f) p‖ ≤
      24 * ((2 : ℝ)^45 * C) * Real.exp (-Real.sqrt (400 * ‖p‖ / (2*A)) / 64) := by
  have hA0 : 0 < A := (by positivity : (0 : ℝ) < 2^156).trans_le hA
  apply angularFourier_gevrey_decay (cutoffSymbol f) (cutoffSymbol_local_contDiff f hf)
    (cutoffSymbol_compact f) ((cutoffSymbol_tsupport f).trans
      (closedBall_subset_closedBall (by norm_num [smallRadius, backgroundAmplitude])))
    (by positivity) (by positivity)
  intro K q v hv
  exact cutoffSymbol_local_gevrey f hf hC.le hA hd q v hv K

#print axioms cutoffSymbol_local_gevrey
#print axioms cutoffSymbol_local_fourier_decay

end Maxwell.Continuum.Auxiliary
