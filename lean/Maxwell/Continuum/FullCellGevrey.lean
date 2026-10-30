import Maxwell.Continuum.FullCellSymbolDerivatives

/-! All-order Gevrey and summable Fourier decay of the complete cutoff
cell inverse. The pole scale h is retained in the derivative radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open FreeFiber Auxiliary PeriodicBand OperatorFourier Set Metric Filter
open scoped Topology

local instance fullCellGevreyRealSpace : NormedSpace ℝ CellMap := NormedSpace.complexToReal

attribute [local irreducible] fullCellSymbol

theorem cutoffFullCellSymbol_tsupport_sup (z σ : ℝ) :
    tsupport (cutoffFullCellSymbol z σ) ⊆
      {q | ‖realMomentumMap q‖ ≤ 2 * smallRadius} := by
  apply closure_minimal _ (isClosed_le realMomentumMap.continuous.norm continuous_const)
  intro q hq
  have hc : cutoff q ≠ 0 := by
    intro he
    apply (Function.mem_support.mp hq)
    unfold cutoffFullCellSymbol cutoffSymbol
    rw [he, Complex.ofReal_zero]
    exact zero_smul ℂ (realSymbol (fullCellSymbol z σ) q)
  exact cutoff_ne_zero_sup_le hc

theorem cutoffFullCellSymbol_contDiff {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffFullCellSymbol z σ) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius
  · exact (Complex.ofRealCLM.contDiff.comp (Well.chi_contDiff smallRadius)).contDiffAt.smul
      (realFullCellSymbol_contDiffAt D hh hσ0 hσ (hq.trans (by linarith [smallRadius_pos])))
  · have hq' : 2 * smallRadius < ‖realMomentumMap q‖ := by
      linarith [lt_of_not_ge hq, smallRadius_pos]
    have he : ∀ᶠ p : Space in 𝓝 q, 2 * smallRadius < ‖realMomentumMap p‖ :=
      realMomentumMap.continuous.norm.continuousAt.eventually (eventually_gt_nhds hq')
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [he] with p hp
    have hz : cutoff p = 0 := by
      by_contra hn
      exact (not_lt_of_ge (cutoff_ne_zero_sup_le hn)) hp
    unfold cutoffFullCellSymbol cutoffSymbol
    rw [hz, Complex.ofReal_zero]
    exact zero_smul ℂ (realSymbol (fullCellSymbol z σ) p)

theorem fullCell_gevrey_rate {h z : ℝ} (D : Calibration h z) :
    (2 : ℝ)^156 ≤ (2 : ℝ)^256 / h := by
  apply (le_div_iff₀ D.h_pos).mpr
  have hh : h ≤ 1 := (calibration_h_small D).trans (by norm_num)
  calc
    _ ≤ (2 : ℝ)^156 * 1 := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ _ := by norm_num

theorem cutoffFullCellSymbol_gevrey {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖directionalDerivative K (cutoffFullCellSymbol z σ) q v‖ ≤
      ((2 : ℝ)^59 * (h^2)⁻¹) * ((2 : ℝ)^257 / h)^K * (K.factorial : ℝ)^2 := by
  have hpos := D.h_pos
  by_cases hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius
  · let a : ℝ → ℝ := fun s => cutoff (q + s • v)
    let b : ℝ → CellMap := fun s => realSymbol (fullCellSymbol z σ) (q + s • v)
    have ha : ContDiff ℝ (⊤ : ℕ∞) a := (Well.chi_contDiff smallRadius).comp (by fun_prop)
    have hb : ContDiffAt ℝ (⊤ : ℕ∞) b 0 := by
      have hat : ContDiffAt ℝ (⊤ : ℕ∞) (realSymbol (fullCellSymbol z σ))
          (q + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using realFullCellSymbol_contDiffAt D hh hσ0 hσ
          (hq.trans (by linarith [smallRadius_pos]))
      simpa only [Function.comp_def] using hat.comp 0
        (show ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => q + s • v) 0 by fun_prop)
    have hab (n : ℕ) : |iteratedDeriv n a 0| ≤
        (2 : ℝ)^45 * ((2 : ℝ)^256 / h)^n * (n.factorial : ℝ)^2 := by
      have hd := Well.chi_directional_gevrey smallRadius smallRadius_pos q v hv n
      rw [Well.directionalDerivative_eq_line n (Well.chi smallRadius)
        (Well.chi_contDiff smallRadius)] at hd
      have hc : (2 : ℝ)^16 / smallRadius = (2 : ℝ)^156 := by
        norm_num [smallRadius, backgroundAmplitude]
      rw [hc] at hd
      exact hd.trans (by gcongr; exact fullCell_gevrey_rate D)
    have hbb (n : ℕ) : ‖iteratedDeriv n b 0‖ ≤
        ((2 : ℝ)^14 * (h^2)⁻¹) * ((2 : ℝ)^256 / h)^n * (n.factorial : ℝ)^2 :=
      realFullCellSymbol_line_bound D hh hσ0 hσ hq hv n
    have hd := gevrey_smul a b 0 ha.contDiffAt hb (2^45) (2^14 * (h^2)⁻¹)
      (2^256 / h) (by positivity) (by positivity) (by positivity) hab hbb K
    rw [directionalDerivative_eq_line K (cutoffFullCellSymbol z σ)
      (cutoffFullCellSymbol_contDiff D hh hσ0 hσ)]
    have he : (fun s : ℝ => cutoffFullCellSymbol z σ (q + s • v)) =
        (fun s => a s • b s) := rfl
    rw [he]
    have hc : (2 : ℝ)^45 * ((2 : ℝ)^14 * (h^2)⁻¹) = (2 : ℝ)^59 * (h^2)⁻¹ := by ring
    have hr : 2 * ((2 : ℝ)^256 / h) = (2 : ℝ)^257 / h := by ring
    rw [hc, hr] at hd
    exact hd
  · have hz : iteratedFDeriv ℝ K (cutoffFullCellSymbol z σ) q = 0 := by
      apply Function.notMem_support.mp
      intro hm
      have hs := cutoffFullCellSymbol_tsupport_sup z σ (support_iteratedFDeriv_subset K hm)
      exact hq (hs.trans (by linarith [smallRadius_pos]))
    unfold directionalDerivative
    rw [hz]
    simp only [zero_apply, norm_zero]
    positivity

theorem cutoffFullCellSymbol_fourier_decay {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (p : Space) :
    ‖angularFourier (cutoffFullCellSymbol z σ) p‖ ≤
      24 * ((2 : ℝ)^59 * (h^2)⁻¹) *
        Real.exp (-Real.sqrt (400 * ‖p‖ / ((2 : ℝ)^257 / h)) / 64) := by
  have hpos := D.h_pos
  apply angularFourier_gevrey_decay (cutoffFullCellSymbol z σ)
    (cutoffFullCellSymbol_contDiff D hh hσ0 hσ) (cutoffSymbol_compact (fullCellSymbol z σ))
    ((cutoffSymbol_tsupport (fullCellSymbol z σ)).trans
      (closedBall_subset_closedBall (by norm_num [smallRadius, backgroundAmplitude])))
    (by positivity) (by positivity)
  intro K q v hv
  exact cutoffFullCellSymbol_gevrey D hh hσ0 hσ q v hv K

#print axioms cutoffFullCellSymbol_gevrey
#print axioms cutoffFullCellSymbol_fourier_decay

end Maxwell.Continuum.CellGauge
