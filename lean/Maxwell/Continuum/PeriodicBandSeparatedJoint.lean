import Maxwell.Continuum.PeriodicBandSeparatedJointBasic

/-! Joint operator-norm holomorphy of the actual full separated inverse,
including the band. The proof uses a bounded reference resolvent and
Banach-algebra inversion, not a common unbounded momentum domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic Metric Set Filter
open scoped Topology

theorem referenceSeparated_analytic : AnalyticOnNhd ℂ referenceSeparated chart := by
  intro t ht
  have hR : AnalyticAt ℂ (fun s => fullResolventExtension (s, referenceEnergy)) t :=
    (fullResolventExtension_analytic_wide ht (energyDisk_wide referenceEnergy_mem)
      (referenceEnergy_ne_band ht)).comp₂ analyticAt_id analyticAt_const
  have hQ : AnalyticAt ℂ fullBandComplement t :=
    analyticAt_const.sub (fullSpectralProjection_analytic t ht)
  exact hR.mul hQ

theorem separatedDenominator_analytic {z : Parameter} (ht : z.1 ∈ chart) :
    AnalyticAt ℂ separatedDenominator z := by
  have hA : AnalyticAt ℂ (fun w : Parameter => referenceSeparated w.1) z :=
    AnalyticAt.comp (f := fun w : Parameter => w.1)
      (referenceSeparated_analytic z.1 ht) analyticAt_fst
  have hd : AnalyticAt ℂ (fun w : Parameter => (backgroundAmplitude : ℂ) * (w.2 - referenceEnergy)) z :=
    (analyticAt_const (v := (backgroundAmplitude : ℂ))).mul (analyticAt_snd.sub analyticAt_const)
  exact analyticAt_const.sub (hd.smul hA)

/-- A total formula holomorphic at every valid energy, including the band. -/
theorem jointSeparatedResolvent_analyticAt {z : Parameter} (ht : z.1 ∈ chart)
    (he : z.2 ∈ energyDisk) : AnalyticAt ℂ jointSeparatedResolvent z := by
  have hA : AnalyticAt ℂ (fun w : Parameter => referenceSeparated w.1) z :=
    AnalyticAt.comp (f := fun w : Parameter => w.1)
      (referenceSeparated_analytic z.1 ht) analyticAt_fst
  have hinv : AnalyticAt ℂ (fun A : FiberMap => Ring.inverse A) (separatedDenominator z) := by
    obtain ⟨U, hU⟩ := separatedDenominator_isUnit ht he
    rw [← hU]
    exact analyticAt_inverse (𝕜 := ℂ) (A := FiberMap) U
  exact hA.mul (AnalyticAt.comp (f := separatedDenominator) hinv (separatedDenominator_analytic ht))

theorem jointSeparatedResolvent_analytic :
    AnalyticOnNhd ℂ jointSeparatedResolvent (chart ×ˢ energyDisk) :=
  fun _ hz => jointSeparatedResolvent_analyticAt hz.1 hz.2

/-- Joint holomorphy of the original pole-subtracted full resolvent itself. -/
theorem fullSeparatedResolvent_joint_analytic :
    AnalyticOnNhd ℂ (fun z : Parameter => fullSeparatedResolvent z.1 z.2)
      (chart ×ˢ ball (Corner.lambdaStar : ℂ) (1 / 100)) := by
  intro z hz
  have he : z.2 ∈ energyDisk := ball_subset_closedBall hz.2
  apply (jointSeparatedResolvent_analyticAt hz.1 he).congr
  have hev : ∀ᶠ w in 𝓝 z, w ∈ chart ×ˢ ball (Corner.lambdaStar : ℂ) (1 / 100) :=
    (chart_isOpen.prod isOpen_ball).mem_nhds hz
  filter_upwards [hev] with w hw
  exact jointSeparatedResolvent_eq hw.1 (ball_subset_closedBall hw.2)

theorem jointSeparatedResolvent_norm_le {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ closedBall (scaledBand t) (1 / 200)) :
    ‖jointSeparatedResolvent (t, e)‖ ≤ (2 : ℝ) ^ 112 := by
  rw [jointSeparatedResolvent_eq ht (centeredEnergyDisk_subset ht he)]
  exact fullSeparatedResolvent_norm_le ht he

end Maxwell.Continuum.PeriodicBand
