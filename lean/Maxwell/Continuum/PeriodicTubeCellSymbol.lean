import Maxwell.Continuum.PeriodicTubeInverseBounds
import Maxwell.Continuum.CellSeparatedSymbol

/-! The complete inverse in the literal within-cell Bloch gauge. These
are operator-norm holomorphic maps on the full cell L² space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber PeriodicBand FiberAnalytic Auxiliary CellBandFourier

attribute [local irreducible] fullFiberResolvent fullSpectralProjection separatedSymbol
  dielectricBand shiftedMomentum hessianEnergy antiGauge antiUngauge conjugate

def selectedCellProjection (q : Momentum) : CellMap :=
  (antiGauge q).comp ((conjugate (fullSpectralProjection (unscale q))).comp (antiUngauge q))

def fullCellSymbol (z σ : ℝ) (q : Momentum) : CellMap :=
  (antiGauge q).comp ((conjugate (fullFiberResolvent z σ q)).comp (antiUngauge q))

theorem fullCellSymbol_apply (z σ : ℝ) (q : Momentum) (u : CellFieldL2) :
    fullCellSymbol z σ q u = antiGauge q
      (CellFourier.unitary (fullFiberResolvent z σ q
        (CellFourier.unitary.symm (antiUngauge q u)))) := by
  change antiGauge q (conjugate (fullFiberResolvent z σ q) (antiUngauge q u)) = _
  rw [conjugate_apply]

theorem fullCellSymbol_pole_formula {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius)
    (hne : dielectricBand q - ((z + σ : ℝ) : ℂ) ≠ 0) :
    fullCellSymbol z σ q =
      (dielectricBand q - ((z + σ : ℝ) : ℂ))⁻¹ • selectedCellProjection q +
        separatedCellSymbol z σ q := by
  rw [fullCellSymbol, fullFiberResolvent_pole_formula D hσ0 hσ hq hne,
    map_add, map_smul, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
  rfl

theorem fullCellSymbol_analyticAt {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius)
    (hne : dielectricBand q - ((z + σ : ℝ) : ℂ) ≠ 0) :
    AnalyticAt ℂ (fullCellSymbol z σ) q := by
  have hs := (conjugate.analyticAt (fullFiberResolvent z σ q)).comp
    (f := fullFiberResolvent z σ) (fullFiberResolvent_analyticAt D hσ0 hσ hq hne)
  exact ((antiGauge_analytic q).contDiffAt.clm_comp
    (hs.contDiffAt.clm_comp (antiUngauge_analytic q).contDiffAt)).analyticAt

theorem fullCellSymbol_tube_analyticAt {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    AnalyticAt ℂ (fullCellSymbol z σ) (shiftedMomentum q b) :=
  fullCellSymbol_analyticAt D hσ0 hσ
    (tube_momentum_norm_le D.h_pos.le hh q b hq hb)
    (tube_denominator_ne_zero D hh hσ q b hq hb)

theorem fullCellSymbol_tube_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖fullCellSymbol z σ (shiftedMomentum q b)‖ ≤ (2 : ℝ)^14 * (h^2)⁻¹ := by
  have hqs := tube_momentum_norm_le D.h_pos.le hh q b hq hb
  have hg := cellGauge_small_bound hqs
  have hs := (conjugate_bound (fullFiberResolvent z σ (shiftedMomentum q b))).trans
    (fullFiberResolvent_tube_norm_le D hh hσ0 hσ q b hq hb)
  unfold fullCellSymbol
  calc
    _ ≤ ‖antiGauge (shiftedMomentum q b)‖ *
        ‖(conjugate (fullFiberResolvent z σ (shiftedMomentum q b))).comp
          (antiUngauge (shiftedMomentum q b))‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 3 * (((2 : ℝ)^10 * (h^2)⁻¹) * 3) := by
      apply mul_le_mul hg.1 _ (norm_nonneg _) (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hs hg.2 (norm_nonneg _) (by positivity))
    _ = (9 * (2 : ℝ)^10) * (h^2)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr (sq_nonneg h))

end Maxwell.Continuum.CellGauge
