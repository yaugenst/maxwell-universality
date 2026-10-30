import Maxwell.Continuum.CellSourceTube

/-! The actual compact-source matrix element on the limiting pole
contour. Dominated convergence is proved with the physical cell packet,
including its momentum dependence on both sides of the resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand CellBandFourier EffectiveMass Bloch Auxiliary AlmostAnalytic
  Set MeasureTheory Filter
open scoped Topology

attribute [local irreducible] fullCellSymbol poleContourIntegrand

def sourcePoleContourIntegrand {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) (R : Space) (s : ℝ) (q : Space) : ℂ :=
  contourProduct (cutoffOrder (poleContourShift D hh j)) (poleContourShift D hh j)
    (phasedSymbol R (cellSourcePairing h u v (fullCellSymbol z 0))) s q

theorem sourcePoleContourIntegrand_inner {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) (R : Space) (s : ℝ) (q : Space) :
    sourcePoleContourIntegrand D hh j u v R s q =
      inner ℂ (cellSourcePacket h u (star (AlmostAnalytic.shiftedMomentum q (poleContourShift D hh j) s)))
        (poleContourIntegrand D hh j R s q
          (cellSourcePacket h v (AlmostAnalytic.shiftedMomentum q (poleContourShift D hh j) s))) := by
  rw [sourcePoleContourIntegrand, poleContourIntegrand, contourProduct, contourProduct,
    phasedSymbol, phasedSymbol, cellSourcePairing_eq_inner, smul_apply, smul_apply,
    inner_smul_right, inner_smul_right]
  rfl

theorem sourcePoleContourIntegrand_joint_continuousAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) (R : Space)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {q : Space} (hq : q ≠ 0) :
    ContinuousAt (Function.uncurry (sourcePoleContourIntegrand D hh j u v R)) (s,q) := by
  let p : ℝ × Space → Momentum := fun x => AlmostAnalytic.shiftedMomentum x.2 (poleContourShift D hh j) x.1
  have hp : Continuous p := by unfold p AlmostAnalytic.shiftedMomentum; fun_prop
  have hu : ContinuousAt (fun x => cellSourcePacket h u (star (p x))) (s,q) :=
    (cellSourcePacket_analytic h u _).continuousAt.comp (continuous_star.comp hp).continuousAt
  have hv : ContinuousAt (fun x => cellSourcePacket h v (p x)) (s,q) :=
    (cellSourcePacket_analytic h v _).continuousAt.comp hp.continuousAt
  have hY := poleContourIntegrand_joint_continuousAt D hh j R hs hq
  convert hu.inner (hY.clm_apply hv) using 1
  funext x
  exact sourcePoleContourIntegrand_inner D hh j u v R x.1 x.2

theorem sourcePoleContourIntegrand_stronglyMeasurable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (u v : FieldL2) (R : Space)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    StronglyMeasurable (sourcePoleContourIntegrand D hh j u v R s) := by
  apply ContinuousOn.stronglyMeasurable_of_countable_compl (s := ({0} : Set Space)ᶜ)
  · intro q hq
    exact ((sourcePoleContourIntegrand_joint_continuousAt D hh j u v R hs hq).comp
      (f := fun p : Space => (s,p)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  · simpa only [compl_compl] using countable_singleton (0 : Space)

theorem sourcePoleContourIntegrand_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D hh j) R)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {q : Space} (hq : q ≠ 0) :
    ‖sourcePoleContourIntegrand D hh j u v R s q‖ ≤
      (2 : ℝ)^90*(h⁻¹)^3*poleContourMajorant q := by
  rw [sourcePoleContourIntegrand_inner]
  have hh0 := D.h_pos
  exact (cellSource_inner_tube_norm D.h_pos (hh.trans (by norm_num)) hu hv
    (sourceImaginary_poleContour D hh j q hs) _).trans
      (mul_le_mul_of_nonneg_left (poleContourIntegrand_norm_le D hh j R hphase hs hq) (by positivity))

theorem sourcePoleContourIntegrand_integrable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D hh j) R)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Integrable (sourcePoleContourIntegrand D hh j u v R s) volume := by
  apply (poleContourMajorant_integrable.const_mul ((2 : ℝ)^90*(h⁻¹)^3)).mono'
    (sourcePoleContourIntegrand_stronglyMeasurable D hh j u v R hs).aestronglyMeasurable
  filter_upwards [volume.ae_ne (0 : Space)] with q hq
  exact sourcePoleContourIntegrand_norm_le D hh j hu hv R hphase hs hq

theorem sourcePoleContour_integral_tendsto {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D hh j) R) :
    Tendsto (fun s : ℝ => ∫ q, sourcePoleContourIntegrand D hh j u v R s q)
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ q, sourcePoleContourIntegrand D hh j u v R 1 q)) := by
  rw [← nhdsWithin_Ico_eq_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
  apply tendsto_integral_filter_of_dominated_convergence
    (fun q => (2 : ℝ)^90*(h⁻¹)^3*poleContourMajorant q)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (sourcePoleContourIntegrand_stronglyMeasurable D hh j u v R ⟨hs.1, hs.2.le⟩).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [volume.ae_ne (0 : Space)] with q hq
    exact sourcePoleContourIntegrand_norm_le D hh j hu hv R hphase ⟨hs.1, hs.2.le⟩ hq
  · exact poleContourMajorant_integrable.const_mul _
  · filter_upwards [volume.ae_ne (0 : Space)] with q hq
    exact ((sourcePoleContourIntegrand_joint_continuousAt D hh j u v R
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) hq).comp
      (f := fun t : ℝ => (t,q)) (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt

#print axioms sourcePoleContour_integral_tendsto

end Maxwell.Continuum.CellGauge
