import Maxwell.Continuum.PeriodicTube
import Maxwell.Continuum.SeparatedSymbolAnalytic
import Maxwell.Continuum.AuxiliaryFiberInverse

/-! The full maximal-domain Maxwell fiber inverse at complex momentum.
Its pole term is the actual full spectral projection; its remainder is
the previously constructed separated inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic Metric

attribute [local irreducible] fullResolventExtension scaledBand dielectricBand
  fullSeparatedResolvent fullSpectralProjection fullPoleResidue separatedSymbol

def fullFiberResolvent (z σ : ℝ) (q : Momentum) : FiberMap :=
  fullResolventExtension (unscale q, sampledScaledEnergy z σ)

theorem sampledEnergy_complex_difference (z σ : ℝ) (q : Momentum) :
    sampledEnergy z σ - physicalBand (unscale q) =
      -(dielectricBand q - ((z + σ : ℝ) : ℂ)) := by
  unfold sampledEnergy dielectricBand
  push_cast
  ring

theorem sampledScaledEnergy_ne_band_of_denominator (z σ : ℝ) (q : Momentum)
    (hne : dielectricBand q - ((z + σ : ℝ) : ℂ) ≠ 0) :
    sampledScaledEnergy z σ ≠ scaledBand (unscale q) := by
  apply scaledEnergy_ne_band
  intro he
  have hd := sampledEnergy_complex_difference z σ q
  rw [he, sub_self] at hd
  exact hne (neg_eq_zero.mp hd.symm)

theorem complex_sampledFiber_eq (z σ : ℝ) (q : Momentum) :
    materialFiber (scaledMomentum (unscale q))
      (totalEnergy (sampledScaledEnergy z σ)) backgroundAmplitude =
      materialFiber q (sampledEnergy z σ) backgroundAmplitude := by
  rw [scaledMomentum_unscale, sampledScaledEnergy, totalEnergy_scaledEnergy]

theorem complex_sampledScaledEnergy_wide {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    ‖sampledScaledEnergy z σ - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50 :=
  energyDisk_wide (centeredEnergyDisk_subset (separated_unscale_chart hq)
    (sampledScaledEnergy_near_complex_band D hσ0 hσ hq))

/-- A two-sided inverse on the literal infinite-fiber maximal domain. -/
def complexFiberInverse {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius)
    (hne : dielectricBand q - ((z + σ : ℝ) : ℂ) ≠ 0) :
    SelfAdjointResolvent.BoundedInverse
      (materialFiber q (sampledEnergy z σ) backgroundAmplitude) :=
  transportedInverse (complex_sampledFiber_eq z σ q)
    (inverseAwayFromBand (separated_unscale_chart hq)
      (complex_sampledScaledEnergy_wide D hσ0 hσ hq)
      (sampledScaledEnergy_ne_band_of_denominator z σ q hne))

theorem fullFiberResolvent_eq_inverse {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius)
    (hne : dielectricBand q - ((z + σ : ℝ) : ℂ) ≠ 0) :
    fullFiberResolvent z σ q = (complexFiberInverse D hσ0 hσ hq hne).map := by
  rw [complexFiberInverse, transportedInverse_map]
  exact fullResolventExtension_eq_inverseAwayFromBand (separated_unscale_chart hq)
    (complex_sampledScaledEnergy_wide D hσ0 hσ hq)
    (sampledScaledEnergy_ne_band_of_denominator z σ q hne)

theorem fullFiberResolvent_pole_formula {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius)
    (hne : dielectricBand q - ((z + σ : ℝ) : ℂ) ≠ 0) :
    fullFiberResolvent z σ q =
      (dielectricBand q - ((z + σ : ℝ) : ℂ))⁻¹ • fullSpectralProjection (unscale q) +
        separatedSymbol z σ q := by
  have hd : (backgroundAmplitude : ℂ) *
      (sampledScaledEnergy z σ - scaledBand (unscale q)) =
        -(dielectricBand q - ((z + σ : ℝ) : ℂ)) := by
    rw [← totalEnergy_sub, sampledScaledEnergy, totalEnergy_scaledEnergy]
    exact sampledEnergy_complex_difference z σ q
  rw [fullFiberResolvent, fullResolvent_pole_formula (separated_unscale_chart hq)
    (centeredEnergyDisk_subset (separated_unscale_chart hq)
      (sampledScaledEnergy_near_complex_band D hσ0 hσ hq))
    (sampledScaledEnergy_ne_band_of_denominator z σ q hne), hd,
    separatedSymbol_eq D hσ0 hσ hq]
  simp only [inv_neg, fullSpectralProjection, smul_neg]
  exact congrArg (fun T : FiberMap =>
    T + fullSeparatedResolvent (unscale q) (sampledScaledEnergy z σ))
    (neg_smul (dielectricBand q - ((z + σ : ℝ) : ℂ))⁻¹ (fullPoleResidue (unscale q)))

theorem fullFiberResolvent_analyticAt {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius)
    (hne : dielectricBand q - ((z + σ : ℝ) : ℂ) ≠ 0) :
    AnalyticAt ℂ (fullFiberResolvent z σ) q := by
  have hu : AnalyticAt ℂ unscale q :=
    ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := Momentum) (F := Momentum)
      ((backgroundAmplitude : ℂ)⁻¹ • ContinuousLinearMap.id ℂ Momentum) q
  exact AnalyticAt.comp (f := fun q : Momentum => (unscale q, sampledScaledEnergy z σ))
    (fullResolventExtension_analytic_wide (separated_unscale_chart hq)
      (complex_sampledScaledEnergy_wide D hσ0 hσ hq)
      (sampledScaledEnergy_ne_band_of_denominator z σ q hne))
    (hu.prod analyticAt_const)

end Maxwell.Continuum.Auxiliary
