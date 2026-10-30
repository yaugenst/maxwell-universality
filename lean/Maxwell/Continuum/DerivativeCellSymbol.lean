import Maxwell.Continuum.AuxiliaryDerivativeResolvent
import Maxwell.Continuum.FullCellCauchyGeometry

/-! The literal derivative-resolvent symbol, including every alias and
the physical within-cell gauge. Its holomorphy follows from the actual
maximal-domain inverse, with no common-domain assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber FiberAnalytic Auxiliary PeriodicBand CellBandFourier

attribute [local irreducible] fullFiberResolvent antiGauge antiUngauge conjugate

def derivativeFiberSymbol (z σ : ℝ) (j : Fin 3) (q : Momentum) : FiberMap :=
  (fullFiberResolvent z σ q).comp
    ((PeriodicMaterial.derivativeFiber j).comp (fullFiberResolvent z σ q))

def derivativeCellSymbol (z σ : ℝ) (j : Fin 3) (q : Momentum) : CellMap :=
  (antiGauge q).comp ((conjugate (derivativeFiberSymbol z σ j q)).comp (antiUngauge q))

def cutoffDerivativeCellSymbol (z σ : ℝ) (j : Fin 3) : Space → CellMap :=
  cutoffSymbol (derivativeCellSymbol z σ j)

theorem derivativeFiberSymbol_tube_analyticAt {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    AnalyticAt ℂ (derivativeFiberSymbol z σ j) (shiftedMomentum q b) := by
  have ha := fullFiberResolvent_tube_analyticAt D hh hσ0 hσ q b hq hb
  exact (ha.contDiffAt.clm_comp (contDiffAt_const.clm_comp ha.contDiffAt)).analyticAt

theorem derivativeCellSymbol_tube_analyticAt {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    AnalyticAt ℂ (derivativeCellSymbol z σ j) (shiftedMomentum q b) := by
  have hs := (conjugate.analyticAt (derivativeFiberSymbol z σ j (shiftedMomentum q b))).comp
    (f := derivativeFiberSymbol z σ j) (derivativeFiberSymbol_tube_analyticAt D hh hσ0 hσ j q b hq hb)
  exact ((antiGauge_analytic _).contDiffAt.clm_comp
    (hs.contDiffAt.clm_comp (antiUngauge_analytic _).contDiffAt)).analyticAt

theorem derivativeFiberSymbol_tube_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖derivativeFiberSymbol z σ j (shiftedMomentum q b)‖ ≤
      (28 * (2 : ℝ)^20) * (h^4)⁻¹ := by
  have hR := fullFiberResolvent_tube_norm_le D hh hσ0 hσ q b hq hb
  unfold derivativeFiberSymbol
  calc
    _ ≤ ‖fullFiberResolvent z σ (shiftedMomentum q b)‖ *
        ‖(PeriodicMaterial.derivativeFiber j).comp (fullFiberResolvent z σ (shiftedMomentum q b))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((2 : ℝ)^10 * (h^2)⁻¹) * (28 * ((2 : ℝ)^10 * (h^2)⁻¹)) := by
      apply mul_le_mul hR _ (norm_nonneg _) (by positivity)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (PeriodicMaterial.derivativeFiber_norm_le j) hR (norm_nonneg _) (by norm_num))
    _ = _ := by simp only [← inv_pow]; ring

theorem derivativeCellSymbol_tube_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (j : Fin 3) (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖derivativeCellSymbol z σ j (shiftedMomentum q b)‖ ≤ (2 : ℝ)^32 * (h^4)⁻¹ := by
  have hg := cellGauge_small_bound (tube_momentum_norm_le D.h_pos.le hh q b hq hb)
  have hR := (conjugate_bound (derivativeFiberSymbol z σ j (shiftedMomentum q b))).trans
    (derivativeFiberSymbol_tube_norm_le D hh hσ0 hσ j q b hq hb)
  unfold derivativeCellSymbol
  calc
    _ ≤ ‖antiGauge (shiftedMomentum q b)‖ *
        ‖(conjugate (derivativeFiberSymbol z σ j (shiftedMomentum q b))).comp
          (antiUngauge (shiftedMomentum q b))‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 3 * (((28 * (2 : ℝ)^20) * (h^4)⁻¹) * 3) := by
      apply mul_le_mul hg.1 _ (norm_nonneg _) (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hR hg.2 (norm_nonneg _) (by positivity))
    _ = (252 * (2 : ℝ)^20) * (h^4)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

#print axioms derivativeCellSymbol_tube_analyticAt
#print axioms derivativeCellSymbol_tube_norm_le

end Maxwell.Continuum.CellGauge
