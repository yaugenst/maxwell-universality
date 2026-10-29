import Maxwell.Continuum.PeriodicTubeCellSymbol
import Maxwell.Continuum.SeparatedCellKernel

/-! Exact physical matrix elements of the complete cutoff resolvent in
the literal spatial cell gauge. Every alias is retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber FiberAnalytic CellBandFourier Auxiliary Bloch MeasureTheory PeriodicBand
open scoped Topology

attribute [local irreducible] fullFiberResolvent fiberResolvent fullCellSymbol Bloch.unitary

def cutoffFullCellSymbol (z σ : ℝ) : Space → CellMap := cutoffSymbol (fullCellSymbol z σ)

theorem fullFiberResolvent_real (z σ : ℝ) (q : Corner.Vec) :
    fullFiberResolvent z σ (realMomentum q) = fiberResolvent z σ q := by
  unfold fullFiberResolvent fiberResolvent fiberParameter
  rfl

theorem fullFiberResolvent_realMap (z σ : ℝ) (q : Space) :
    fullFiberResolvent z σ (realMomentumMap q) = fiberResolvent z σ (fun j => q j) :=
  fullFiberResolvent_real z σ (fun j => q j)

theorem cutoffFullCellSymbol_apply (z σ : ℝ) (q : QuasiCell) (f : CellFieldL2) :
    cutoffFullCellSymbol z σ q.val f = antiGauge (quasiMomentum q)
      (conjugate (cutoffFiber z σ q) (antiUngauge (quasiMomentum q) f)) := by
  by_cases hq : q ∈ cutoffRegion
  · rw [cutoffFiber_eq hq]
    unfold cutoffFullCellSymbol cutoffSymbol realSymbol fullCellSymbol
    change (cutoff q.val : ℂ) • antiGauge (quasiMomentum q)
      (conjugate (fullFiberResolvent z σ (quasiMomentum q)) (antiUngauge (quasiMomentum q) f)) = _
    change (cutoff q.val : ℂ) • antiGauge (quasiMomentum q)
      (conjugate (fullFiberResolvent z σ (realMomentum (fun j => q.val j)))
        (antiUngauge (quasiMomentum q) f)) = _
    rw [fullFiberResolvent_real, map_smul, smul_apply, map_smul]
  · rw [cutoffFiber_zero hq]
    unfold cutoffFullCellSymbol cutoffSymbol
    rw [cutoff_eq_zero_outside hq, Complex.ofReal_zero]
    rw [zero_smul ℂ (realSymbol (fullCellSymbol z σ) q.val)]
    simp only [zero_apply, map_zero]

theorem cutoffFullCellSymbol_pairing (z σ : ℝ) (q : QuasiCell) (g f : CellFieldL2) :
    inner ℂ (CellFourier.unitary.symm (antiUngauge (quasiMomentum q) g))
      (cutoffFiber z σ q (CellFourier.unitary.symm (antiUngauge (quasiMomentum q) f))) =
      inner ℂ g (cutoffFullCellSymbol z σ q.val f) := by
  rw [cutoffFullCellSymbol_apply]
  exact gauged_inner (fun j => q.val j) (cutoffFiber z σ q) g f

theorem resolvent_cell_pairing {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) (g f : CellFieldL2) :
    inner ℂ (embedLatticeCell a g) (resolvent D hσ0 hσ (embedLatticeCell b f)) =
      (64 : ℂ) * ∫ q : QuasiCell, (star (latticePhase a q) * latticePhase b q) *
        inner ℂ g (cutoffFullCellSymbol z σ q.val f) ∂quasiMeasure := by
  rw [← unitary_inner, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [unitary_embedLatticeCell a g, unitary_embedLatticeCell b f,
    resolvent_ae D hσ0 hσ (embedLatticeCell b f)] with q hg hf hR
  rw [hg, hR, hf, map_smul, inner_smul_left, inner_smul_right, cutoffFullCellSymbol_pairing]
  simp only [map_mul, map_ofNat, starRingEnd_apply]
  ring

theorem realFullCellSymbol_continuousAt {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) {q : Space}
    (hq : ‖realMomentumMap q‖ ≤ 4 * smallRadius) :
    ContinuousAt (realSymbol (fullCellSymbol z σ)) q := by
  have hp : Continuous (fun p : Space => fun j : Fin 3 => p j) :=
    continuous_pi fun j => PiLp.continuous_apply 2 _ j
  have hR := (fiberResolvent_continuousAt D hσ0 hσ (fun j => q j) hq).comp hp.continuousAt
  have hg := (antiGauge_analytic (realMomentumMap q)).continuousAt.comp realMomentumMap.continuous.continuousAt
  have hgi := (antiUngauge_analytic (realMomentumMap q)).continuousAt.comp realMomentumMap.continuous.continuousAt
  have hc := conjugate.continuous.continuousAt.comp hR
  unfold realSymbol fullCellSymbol
  simp_rw [fullFiberResolvent_realMap]
  exact hg.clm_comp (hc.clm_comp hgi)

theorem cutoffFullCellSymbol_continuous {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) : Continuous (cutoffFullCellSymbol z σ) := by
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius
  · exact (Complex.continuous_ofReal.comp cutoff_continuous).continuousAt.smul
      (realFullCellSymbol_continuousAt D hσ0 hσ (hq.trans (by linarith [smallRadius_pos])))
  · have hq' : 2 * smallRadius < ‖realMomentumMap q‖ := by
      linarith [lt_of_not_ge hq, smallRadius_pos]
    have he : ∀ᶠ p : Space in 𝓝 q, 2 * smallRadius < ‖realMomentumMap p‖ :=
      realMomentumMap.continuous.norm.continuousAt.eventually (eventually_gt_nhds hq')
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [he] with p hp
    have hz : cutoff p = 0 := by
      by_contra hn
      exact (not_lt_of_ge (cutoff_ne_zero_sup_le hn)) hp
    unfold cutoffFullCellSymbol cutoffSymbol
    rw [hz, Complex.ofReal_zero]
    exact zero_smul ℂ (realSymbol (fullCellSymbol z σ) p)

theorem cutoffFullCellSymbol_integrable {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) : Integrable (cutoffFullCellSymbol z σ) :=
  (cutoffFullCellSymbol_continuous D hσ0 hσ).integrable_of_hasCompactSupport
    (cutoffSymbol_compact (fullCellSymbol z σ))

theorem cutoffFullCellSymbol_zero_outside (z σ : ℝ) {q : Space} (hq : q ∉ quasiCell) :
    cutoffFullCellSymbol z σ q = 0 := by
  unfold cutoffFullCellSymbol cutoffSymbol
  rw [cutoff_zero_outside_quasi hq, Complex.ofReal_zero]
  exact zero_smul ℂ (realSymbol (fullCellSymbol z σ) q)

#print axioms resolvent_cell_pairing
#print axioms cutoffFullCellSymbol_integrable

end Maxwell.Continuum.CellGauge
