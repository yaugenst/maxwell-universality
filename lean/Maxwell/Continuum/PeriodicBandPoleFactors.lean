import Maxwell.Continuum.PeriodicBandPhysicalGap
import Maxwell.Continuum.PeriodicBandResolventBounds
import Maxwell.Continuum.RankOneBandPole

/-! Transport of the actual finite Schur pole through the complete
Feshbach inverse. Every factor is a literal bounded map on the infinite
alias space. The physical energy here is total energy, including `+7`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge Metric Set
open scoped ContDiff

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot

theorem actualPerturbation_analytic :
    AnalyticOnNhd ℂ (Function.uncurry (fun t e => perturbation (t, e)))
      (chart ×ˢ closedBall (Corner.lambdaStar : ℂ) (1 / 100)) := chart_energy_analytic

/-- The exact Feshbach embedding of a finite source-to-solution map. -/
def liftFiniteOperator (t : Momentum) (e : ℂ) (J : ClusterMap) : FiberMap :=
  (schurLiftExtension (t, e)).comp (clusterSpace.subtypeL.comp
    (J.comp (adjustedSourceExtension (t, e))))

theorem liftFiniteOperator_sub (t : Momentum) (e : ℂ) (J K : ClusterMap) :
    liftFiniteOperator t e (J - K) = liftFiniteOperator t e J - liftFiniteOperator t e K := by
  ext f
  simp only [liftFiniteOperator, ContinuousLinearMap.comp_apply, sub_apply, map_sub]

theorem liftFiniteOperator_smul (t : Momentum) (e : ℂ) (a : ℂ) (J : ClusterMap) :
    liftFiniteOperator t e (a • J) = a • liftFiniteOperator t e J := by
  ext f
  simp only [liftFiniteOperator, ContinuousLinearMap.comp_apply, smul_apply, map_smul]

def fullPoleNumerator (t : Momentum) (e : ℂ) : FiberMap :=
  liftFiniteOperator t e (actualCornerData.poleNumerator perturbationData t e)

def fullHighSolve (t : Momentum) (e : ℂ) : FiberMap :=
  liftFiniteOperator t e
    (RankOneBand.highSolve finiteK topState Corner.lambdaStar (perturbation (t, e)) e)

/-- The residue with respect to total physical energy, not scaled energy. -/
def fullPoleResidue (t : Momentum) : FiberMap := fullPoleNumerator t (scaledBand t)

def fullSeparatedResolvent (t : Momentum) (e : ℂ) : FiberMap :=
  complementInverseExtension (t, e) + (backgroundAmplitude : ℂ)⁻¹ •
    (dslope (fullPoleNumerator t) (scaledBand t) e - fullHighSolve t e)

theorem finiteSchurInverse_eq_resolvent {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    Ring.inverse (finiteSchurExtension (t, e)) =
      RankOneBand.resolvent finiteK topState Corner.lambdaStar (perturbation (t, e)) e := by
  have he' : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 100 := by
    simpa only [energyDisk, mem_closedBall, dist_eq_norm] using he
  have hV := perturbation_norm_le (t, e) (chart_energy_inBox ht he)
  have hg := actualCornerData.scalarResidual_ne_zero perturbationData t ht e he hne
  rw [finiteSchurExtension_expansion]
  exact (actualCornerData.resolvent_eq_ringInverse (perturbation (t, e)) e hV he' hg).symm

theorem fullResolvent_pole_factor {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    fullResolventExtension (t, e) = complementInverseExtension (t, e) +
      (backgroundAmplitude : ℂ)⁻¹ •
        ((e - scaledBand t)⁻¹ • fullPoleNumerator t e - fullHighSolve t e) := by
  change complementInverseExtension (t, e) + (backgroundAmplitude : ℂ)⁻¹ •
    liftFiniteOperator t e (Ring.inverse (finiteSchurExtension (t, e))) = _
  rw [finiteSchurInverse_eq_resolvent ht he hne,
    actualCornerData.resolvent_pole_factor perturbationData t ht e,
    liftFiniteOperator_sub, liftFiniteOperator_smul]
  simp only [fullPoleNumerator, fullHighSolve, scaledBand]

theorem fullResolvent_pole_formula {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    fullResolventExtension (t, e) =
      ((backgroundAmplitude : ℂ) * (e - scaledBand t))⁻¹ • fullPoleResidue t +
        fullSeparatedResolvent t e := by
  rw [fullResolvent_pole_factor ht he hne]
  unfold fullSeparatedResolvent fullPoleResidue
  rw [dslope_of_ne _ hne, mul_inv]
  simp only [slope_def_module, smul_sub, smul_smul]
  abel

theorem analyticAt_liftFiniteOperator {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (J : ℂ → ClusterMap) (hJ : AnalyticAt ℂ J e) :
    AnalyticAt ℂ (fun f => liftFiniteOperator t f (J f)) e := by
  have hL : AnalyticAt ℂ (fun f => schurLiftExtension (t, f)) e :=
    (analyticAt_schurLiftExtension (t, e) (chart_energy_inBox ht he)).comp₂
      analyticAt_const analyticAt_id
  have hS : AnalyticAt ℂ (fun f => adjustedSourceExtension (t, f)) e :=
    (analyticAt_adjustedSourceExtension (t, e) (chart_energy_inBox ht he)).comp₂
      analyticAt_const analyticAt_id
  exact (hL.contDiffAt.clm_comp
    (contDiffAt_const.clm_comp (hJ.contDiffAt.clm_comp hS.contDiffAt))).analyticAt

theorem analyticAt_fullPoleNumerator {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) : AnalyticAt ℂ (fullPoleNumerator t) e :=
  analyticAt_liftFiniteOperator ht he _
    (actualCornerData.analyticAt_poleNumerator perturbationData actualPerturbation_analytic t ht e he)

theorem analyticAt_fullHighSolve {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) : AnalyticAt ℂ (fullHighSolve t) e := by
  have hV : AnalyticAt ℂ (fun f => perturbation (t, f)) e :=
    (analyticAt_perturbation (t, e) (chart_energy_inBox ht he)).comp₂ analyticAt_const analyticAt_id
  apply analyticAt_liftFiniteOperator ht he
  exact actualCornerData.analyticAt_highSolve (fun f => perturbation (t, f)) id e hV analyticAt_id
    (perturbation_norm_le (t, e) (chart_energy_inBox ht he)) (by
      simpa only [energyDisk, mem_closedBall, dist_eq_norm, id_eq] using he)

/-- The complete infinite-fiber pole is removed in ambient operator norm. -/
theorem analyticAt_fullSeparatedResolvent {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) : AnalyticAt ℂ (fullSeparatedResolvent t) e := by
  have hR : AnalyticAt ℂ (fun f => complementInverseExtension (t, f)) e :=
    (analyticAt_complementInverseExtension (t, e) (chart_energy_inBox ht he)).comp₂
      analyticAt_const analyticAt_id
  have hD := RankOneBand.analyticAt_dslope
    (analyticAt_fullPoleNumerator ht (scaledBand_mem ht)) (analyticAt_fullPoleNumerator ht he)
  exact hR.add ((analyticAt_const (v := (backgroundAmplitude : ℂ)⁻¹)).smul
    (hD.sub (analyticAt_fullHighSolve ht he)))

end Maxwell.Continuum.PeriodicBand
