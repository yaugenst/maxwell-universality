import Maxwell.Continuum.CellSourceAssembly

/-! Joint momentum holomorphy of the literal continuum source factors,
obtained from the finite physical-cell packet and the normalized band. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier EffectiveMass Set
open scoped ContDiff Topology

attribute [local irreducible] normalizedFiberVector physicalFiberVector

theorem selectedCellFunctional_analytic :
    AnalyticOnNhd ℂ selectedCellFunctional physicalChart := by
  intro q hq
  have hv := (physicalFiberVector_analytic q hq).contDiffAt (n := ω)
  have hb : ContDiffAt ℂ ω (fun p => bilinear (physicalFiberVector p)) q :=
    bilinear.contDiff.contDiffAt.comp q hv
  have hu : ContDiffAt ℂ ω (fun p =>
      CellFourier.unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (antiUngauge p)) q :=
    contDiffAt_const.clm_comp (antiUngauge_analytic q).contDiffAt
  convert (hb.clm_comp hu).analyticAt using 1
  funext p
  simp only [selectedCellFunctional, physicalFiberVector]

theorem sourceFactor_joint_analytic {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    AnalyticOnNhd ℂ (sourceFactor h u) physicalChart := by
  intro q hq
  have hn := source_physicalChart_neg hq
  have hfun := (selectedCellFunctional_analytic (-q) hn).comp
    (f := fun p : Momentum => -p) analyticAt_id.neg
  have hpacket := (cellSourcePacket_analytic h u (-q)).comp
    (f := fun p : Momentum => -p) analyticAt_id.neg
  have ha : AnalyticAt ℂ (fun p : Momentum => ((8*fourierNormalization : ℝ) : ℂ)*
      (-I*selectedCellFunctional (-p) (cellSourcePacket h u (-p)))) q := by
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.mul analyticAt_const
    exact (hfun.contDiffAt.clm_apply hpacket.contDiffAt).analyticAt
  apply ha.congr
  filter_upwards [source_physicalChart_isOpen.mem_nhds hq] with p hp
  rw [← cellSourceFunctional_eq (source_physicalChart_neg hp)]
  have he := sourceFactor_eq_cellPacket hh u (source_physicalChart_neg hp)
  simpa only [neg_neg] using he.symm

theorem scaledSourceFactor_joint_analytic {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    AnalyticOnNhd ℂ (scaledSourceFactor h u)
      {k : Momentum | (h : ℂ) • k ∈ physicalChart} := by
  intro k hk
  change AnalyticAt ℂ (fun p : Momentum => (sourceScale h : ℂ)*sourceFactor h u ((h : ℂ) • p)) k
  apply AnalyticAt.mul analyticAt_const
  let H : Momentum →L[ℂ] Momentum := (h : ℂ) • ContinuousLinearMap.id ℂ Momentum
  exact (sourceFactor_joint_analytic hh u _ hk).comp (f := H) (H.analyticAt k)

theorem scaledSourceProduct_joint_analytic {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    AnalyticOnNhd ℂ (scaledSourceProduct h u)
      {k : Momentum | (h : ℂ) • k ∈ physicalChart} := by
  intro k hk
  change AnalyticAt ℂ (fun p : Momentum => scaledSourceFactor h u p*scaledSourceFactor h u (-p)) k
  apply (scaledSourceFactor_joint_analytic hh u k hk).mul
  have hn : (h : ℂ) • (-k) ∈ physicalChart := by
    simpa only [smul_neg] using source_physicalChart_neg hk
  exact (scaledSourceFactor_joint_analytic hh u (-k) hn).comp
    (f := fun p : Momentum => -p) analyticAt_id.neg

#print axioms scaledSourceProduct_joint_analytic

end Maxwell.Continuum.CellGauge
