import Maxwell.Continuum.SeparatedSymbolDerivatives

/-! The literal cutoff times the complete separated inverse is a smooth,
compactly supported Gevrey symbol in operator norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber FiberAnalytic PeriodicBand OperatorFourier Set Metric Filter
open scoped Topology

local instance : NormedSpace ℝ FiberMap := NormedSpace.complexToReal

attribute [local irreducible] separatedSymbol realSeparatedSymbol

def cutoffSeparatedSymbol (z σ : ℝ) (q : Space) : FiberMap :=
  (cutoff q : ℂ) • realSeparatedSymbol z σ q

theorem cutoff_tsupport_bound : tsupport cutoff ⊆ closedBall (0 : Space) (4 * smallRadius) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  simpa only [mem_closedBall, dist_zero_right] using
    cutoff_ne_zero_norm_le (Function.mem_support.mp hq)

theorem cutoffSeparatedSymbol_tsupport (z σ : ℝ) :
    tsupport (cutoffSeparatedSymbol z σ) ⊆ closedBall (0 : Space) (4 * smallRadius) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  have hc : cutoff q ≠ 0 := by
    intro he
    have hz : cutoffSeparatedSymbol z σ q = 0 := by
      rw [cutoffSeparatedSymbol, he, Complex.ofReal_zero]
      exact zero_smul ℂ (realSeparatedSymbol z σ q)
    exact (Function.mem_support.mp hq) hz
  simpa only [mem_closedBall, dist_zero_right] using cutoff_ne_zero_norm_le hc

theorem cutoffSeparatedSymbol_compact (z σ : ℝ) : HasCompactSupport (cutoffSeparatedSymbol z σ) :=
  (isCompact_closedBall (0 : Space) (4 * smallRadius)).of_isClosed_subset isClosed_closure
    (cutoffSeparatedSymbol_tsupport z σ)

theorem cutoff_radius_margin : 4 * smallRadius ≤ separatedRadius / 2 := by
  norm_num [smallRadius, separatedRadius, backgroundAmplitude]

theorem cutoffSeparatedSymbol_contDiff {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffSeparatedSymbol z σ) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : ‖q‖ ≤ separatedRadius / 2
  · have hq' : ‖q‖ ≤ separatedRadius := hq.trans (by linarith [separatedRadius_pos])
    exact (Complex.ofRealCLM.contDiff.comp (Well.chi_contDiff smallRadius)).contDiffAt.smul
      (realSeparatedSymbol_contDiffAt D hσ0 hσ hq')
  · have hq' : 4 * smallRadius < ‖q‖ := lt_of_le_of_lt cutoff_radius_margin (lt_of_not_ge hq)
    have hz : cutoffSeparatedSymbol z σ =ᶠ[𝓝 q] (fun _ => 0) := by
      have he : ∀ᶠ p : Space in 𝓝 q, 4 * smallRadius < ‖p‖ :=
        continuous_norm.continuousAt.eventually (eventually_gt_nhds hq')
      filter_upwards [he] with p hp
      have hc : cutoff p = 0 := by
        by_contra hne
        exact (not_lt_of_ge (cutoff_ne_zero_norm_le hne)) hp
      rw [cutoffSeparatedSymbol, hc, Complex.ofReal_zero]
      exact zero_smul ℂ (realSeparatedSymbol z σ p)
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem cutoffSeparatedSymbol_gevrey {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖OperatorFourier.directionalDerivative K (cutoffSeparatedSymbol z σ) q v‖ ≤
      (2 : ℝ)^160 * ((2 : ℝ)^160)^K * (K.factorial : ℝ)^2 := by
  by_cases hq : ‖q‖ ≤ separatedRadius / 2
  · let f : ℝ → ℝ := fun s => cutoff (q + s • v)
    let g : ℝ → FiberMap := fun s => realSeparatedSymbol z σ (q + s • v)
    have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
      (Well.chi_contDiff smallRadius).comp (by fun_prop)
    have hg : ContDiffAt ℝ (⊤ : ℕ∞) g 0 := by
      have hq' : ‖q‖ ≤ separatedRadius := hq.trans (by linarith [separatedRadius_pos])
      have hat : ContDiffAt ℝ (⊤ : ℕ∞) (realSeparatedSymbol z σ) (q + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using realSeparatedSymbol_contDiffAt D hσ0 hσ hq'
      have hd := hat.comp 0
        (show ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => q + s • v) 0 by fun_prop)
      simpa only [Function.comp_def] using hd
    have hfb (n : ℕ) : |iteratedDeriv n f 0| ≤
        (2 : ℝ)^45 * ((2 : ℝ)^156)^n * (n.factorial : ℝ)^2 := by
      have hd := Well.chi_directional_gevrey smallRadius smallRadius_pos q v hv n
      rw [Well.directionalDerivative_eq_line n (Well.chi smallRadius)
        (Well.chi_contDiff smallRadius)] at hd
      have hc : (2 : ℝ)^16 / smallRadius = (2 : ℝ)^156 := by
        norm_num [smallRadius, backgroundAmplitude]
      rw [hc] at hd
      exact hd
    have hgb (n : ℕ) : ‖iteratedDeriv n g 0‖ ≤
        (2 : ℝ)^112 * ((2 : ℝ)^156)^n * (n.factorial : ℝ)^2 :=
      realSeparatedSymbol_line_bound D hσ0 hσ hq hv n
    have hd := gevrey_smul f g 0 hf.contDiffAt hg (2^45) (2^112) (2^156)
      (by positivity) (by positivity) (by positivity) hfb hgb K
    rw [OperatorFourier.directionalDerivative_eq_line K (cutoffSeparatedSymbol z σ)
      (cutoffSeparatedSymbol_contDiff D hσ0 hσ)]
    have he : (fun s : ℝ => cutoffSeparatedSymbol z σ (q + s • v)) =
        (fun s => f s • g s) := rfl
    rw [he]
    apply hd.trans
    gcongr <;> norm_num
  · have hz : iteratedFDeriv ℝ K (cutoffSeparatedSymbol z σ) q = 0 := by
      apply Function.notMem_support.mp
      intro hm
      have hs := cutoffSeparatedSymbol_tsupport z σ (support_iteratedFDeriv_subset K hm)
      have hs' : ‖q‖ ≤ 4 * smallRadius := by simpa using hs
      exact hq (hs'.trans cutoff_radius_margin)
    unfold OperatorFourier.directionalDerivative
    erw [hz]
    simp only [zero_apply, norm_zero]
    positivity

theorem cutoffSeparatedSymbol_fourier_decay {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (p : Space) :
    ‖angularFourier (cutoffSeparatedSymbol z σ) p‖ ≤
      24 * (2 : ℝ)^160 * Real.exp (-Real.sqrt (400 * ‖p‖ / (2 : ℝ)^160) / 64) := by
  apply angularFourier_gevrey_decay (cutoffSeparatedSymbol z σ)
    (cutoffSeparatedSymbol_contDiff D hσ0 hσ) (cutoffSeparatedSymbol_compact z σ)
    ((cutoffSeparatedSymbol_tsupport z σ).trans
      (closedBall_subset_closedBall (by norm_num [smallRadius, backgroundAmplitude])))
    (by positivity) (by positivity)
  intro K q v hv
  exact cutoffSeparatedSymbol_gevrey D hσ0 hσ q v hv K

#print axioms cutoffSeparatedSymbol_gevrey
#print axioms cutoffSeparatedSymbol_fourier_decay

end Maxwell.Continuum.Auxiliary
