import Maxwell.Continuum.AlmostAnalyticCutoffError
import Maxwell.Continuum.AuxiliaryCutoff

/-! Compact support and transition-shell localization of the literal
almost-analytic cutoff and its defect. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex PeriodicBand Set Metric Filter
open scoped Topology

def cutoffDerivative (n : ℕ) (β : Space) (q : Space) : ℝ :=
  Well.directionalDerivative n (Well.chi smallRadius) q β

theorem cutoff_tsupport : tsupport (Well.chi smallRadius) ⊆
    closedBall (0 : Space) (4*smallRadius) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  simpa only [mem_closedBall, dist_zero_right] using
    Auxiliary.cutoff_ne_zero_norm_le (Function.mem_support.mp hq)

theorem cutoffDerivative_contDiff (n : ℕ) (β : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffDerivative n β) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ n (Well.chi smallRadius)) :=
    (Well.chi_contDiff smallRadius).iteratedFDeriv_right (by
      exact_mod_cast (show (⊤ : ℕ∞) + n ≤ ⊤ from le_top))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Space) ℝ (fun _ => β)).contDiff.comp hd

theorem cutoffDerivative_tsupport (n : ℕ) (β : Space) :
    tsupport (cutoffDerivative n β) ⊆ closedBall (0 : Space) (4*smallRadius) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  apply cutoff_tsupport
  apply support_iteratedFDeriv_subset (𝕜 := ℝ) n
  intro hz
  apply Function.mem_support.mp hq
  unfold cutoffDerivative Well.directionalDerivative
  rw [hz]
  rfl

theorem cutoffDerivative_compact (n : ℕ) (β : Space) : HasCompactSupport (cutoffDerivative n β) :=
  (isCompact_closedBall (0 : Space) (4*smallRadius)).of_isClosed_subset isClosed_closure
    (cutoffDerivative_tsupport n β)

theorem cutoffDerivative_zero_inner {n : ℕ} (hn : n ≠ 0) (β : Space) {q : Space}
    (hq : ‖q‖ < smallRadius) : cutoffDerivative n β q = 0 := by
  have he : Well.chi smallRadius =ᶠ[𝓝 q] (fun _ => (1 : ℝ)) := by
    have hs : ∀ᶠ p : Space in 𝓝 q, ‖p‖ < smallRadius :=
      continuous_norm.continuousAt.eventually (eventually_lt_nhds hq)
    filter_upwards [hs] with p hp
    exact Auxiliary.cutoff_eq_one_of_norm_le hp.le
  unfold cutoffDerivative Well.directionalDerivative
  rw [(he.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds, iteratedFDeriv_const_of_ne hn]
  rfl

theorem cutoffTaylor_contDiff (K : ℕ) (β : Space) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => cutoffTaylor K smallRadius q β s) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (cutoffDerivative_contDiff j β))

theorem cutoffTaylor_tsupport (K : ℕ) (β : Space) (s : ℝ) :
    tsupport (fun q => cutoffTaylor K smallRadius q β s) ⊆
      closedBall (0 : Space) (4*smallRadius) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  by_contra hout
  apply Function.mem_support.mp hq
  unfold cutoffTaylor
  apply Finset.sum_eq_zero
  intro j _
  have hz : cutoffDerivative j β q = 0 := image_eq_zero_of_notMem_tsupport
    (fun hm => hout (cutoffDerivative_tsupport j β hm))
  change coefficient j s * (cutoffDerivative j β q : ℂ) = 0
  rw [hz, Complex.ofReal_zero, mul_zero]

theorem cutoffTaylor_compact (K : ℕ) (β : Space) (s : ℝ) :
    HasCompactSupport (fun q => cutoffTaylor K smallRadius q β s) :=
  (isCompact_closedBall (0 : Space) (4*smallRadius)).of_isClosed_subset isClosed_closure
    (cutoffTaylor_tsupport K β s)

def cutoffDefect (K : ℕ) (β : Space) (s : ℝ) (q : Space) : ℂ :=
  -I * coefficient K s * (cutoffDerivative (K+1) β q : ℂ)

theorem cutoffDefect_contDiff (K : ℕ) (β : Space) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffDefect K β s) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (cutoffDerivative_contDiff (K+1) β))

theorem cutoffDefect_tsupport (K : ℕ) (β : Space) (s : ℝ) :
    tsupport (cutoffDefect K β s) ⊆
      {q : Space | smallRadius ≤ ‖q‖ ∧ ‖q‖ ≤ 4*smallRadius} := by
  apply closure_minimal _ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro q hq
  have hd : cutoffDerivative (K+1) β q ≠ 0 := by
    intro hz
    apply Function.mem_support.mp hq
    simp only [cutoffDefect, hz, Complex.ofReal_zero, mul_zero]
  constructor
  · by_contra hlt
    exact hd (cutoffDerivative_zero_inner (Nat.succ_ne_zero K) β (lt_of_not_ge hlt))
  · have hs := cutoffDerivative_tsupport (K+1) β (subset_closure hd)
    simpa only [mem_closedBall, dist_zero_right, mem_ofPred_eq] using hs

#print axioms cutoffDefect_tsupport

end Maxwell.Continuum.AlmostAnalytic
