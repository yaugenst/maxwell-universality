import Maxwell.Continuum.CellGaugeAlgebra
import Maxwell.Continuum.SeparatedSymbolAnalytic

/-! The separated inverse in the actual within-cell antiperiodic Bloch
gauge, acting on all cell L² fields. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber CellBandFourier FiberAnalytic Auxiliary PeriodicBand Set Metric

attribute [local irreducible] separatedSymbol fullSeparatedResolvent

abbrev CellMap := CellFieldL2 →L[ℂ] CellFieldL2

def conjugateLinear : FiberMap →ₗ[ℂ] CellMap where
  toFun T := CellFourier.unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp CellFourier.unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro u
    exact map_add CellFourier.unitary _ _
  map_smul' c T := by
    apply ContinuousLinearMap.ext
    intro u
    exact map_smul CellFourier.unitary _ _

theorem conjugateLinear_bound (T : FiberMap) : ‖conjugateLinear T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro u
  change ‖CellFourier.unitary (T (CellFourier.unitary.symm u))‖ ≤ ‖T‖ * ‖u‖
  rw [CellFourier.unitary.norm_map]
  simpa only [CellFourier.unitary.symm.norm_map] using T.le_opNorm (CellFourier.unitary.symm u)

def conjugate : FiberMap →L[ℂ] CellMap :=
  conjugateLinear.mkContinuous 1 (fun T => by simpa only [one_mul] using conjugateLinear_bound T)

theorem conjugate_apply (T : FiberMap) (u : CellFieldL2) :
    conjugate T u = CellFourier.unitary (T (CellFourier.unitary.symm u)) := rfl

theorem conjugate_bound (T : FiberMap) : ‖conjugate T‖ ≤ ‖T‖ := conjugateLinear_bound T

def separatedCellSymbol (z σ : ℝ) (q : Momentum) : CellMap :=
  (antiGauge q).comp ((conjugate (separatedSymbol z σ q)).comp (antiUngauge q))

theorem separatedCellSymbol_apply (z σ : ℝ) (q : Momentum) (u : CellFieldL2) :
    separatedCellSymbol z σ q u = antiGauge q
      (CellFourier.unitary (separatedSymbol z σ q (CellFourier.unitary.symm (antiUngauge q u)))) := by
  change antiGauge q (conjugate (separatedSymbol z σ q) (antiUngauge q u)) = _
  rw [conjugate_apply]

theorem separatedCellSymbol_analytic {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) :
    AnalyticOnNhd ℂ (separatedCellSymbol z σ) (closedBall 0 separatedRadius) := by
  intro q hq
  have hs := (conjugate.analyticAt (separatedSymbol z σ q)).comp
    (f := separatedSymbol z σ) (separatedSymbol_analytic D hσ0 hσ q hq)
  exact ((antiGauge_analytic q).contDiffAt.clm_comp
    (hs.contDiffAt.clm_comp (antiUngauge_analytic q).contDiffAt)).analyticAt

theorem cellGauge_small_bound {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    ‖antiGauge q‖ ≤ 3 ∧ ‖antiUngauge q‖ ≤ 3 := by
  have hr : 6 * separatedRadius ≤ 1 := by norm_num [separatedRadius, backgroundAmplitude]
  have he : Real.exp (6 * ‖q‖) ≤ 3 :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans Real.exp_one_lt_three.le
  exact ⟨(antiGauge_norm_le q).trans he, (antiUngauge_norm_le q).trans he⟩

theorem separatedCellSymbol_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    ‖separatedCellSymbol z σ q‖ ≤ (2 : ℝ)^116 := by
  have hg := cellGauge_small_bound hq
  have hs := (conjugate_bound (separatedSymbol z σ q)).trans (separatedSymbol_norm_le D hσ0 hσ hq)
  calc
    _ ≤ ‖antiGauge q‖ * ‖(conjugate (separatedSymbol z σ q)).comp (antiUngauge q)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 3 * ((2 : ℝ)^112 * 3) := by
      apply mul_le_mul hg.1 _ (norm_nonneg _) (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hs hg.2 (norm_nonneg _) (by positivity))
    _ ≤ _ := by norm_num

theorem separatedCellSymbol_eq {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    separatedCellSymbol z σ q = (antiGauge q).comp
      ((conjugate (fullSeparatedResolvent (unscale q) (sampledScaledEnergy z σ))).comp
        (antiUngauge q)) := by
  rw [separatedCellSymbol, separatedSymbol_eq D hσ0 hσ hq]

#print axioms separatedCellSymbol_eq
#print axioms separatedCellSymbol_analytic
#print axioms separatedCellSymbol_norm_le

end Maxwell.Continuum.CellGauge
