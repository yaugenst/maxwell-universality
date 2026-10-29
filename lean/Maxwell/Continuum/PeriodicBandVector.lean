import Maxwell.Continuum.PeriodicBandComparison
import Maxwell.Continuum.ClusterComplementResolventAnalytic
import Maxwell.Continuum.FiberL1Eigenvector

/-! An actual analytic infinite-alias eigenvector, with its maximal-domain
equation and absolute Fourier summability proved for the literal material. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot
  scaledBand clusterVector

def fiberVector (t : Momentum) : FiberSpace :=
  schurLiftExtension (t, scaledBand t) (clusterVector t).val

theorem fiberVector_eq {t : Momentum} (ht : t ∈ chart) :
    fiberVector t = schurLift t (scaledBand t) (chart_closed_bounds ht)
      (chart_energy_inBox ht (scaledBand_mem ht)).2 (clusterVector t).val := by
  unfold fiberVector
  rw [schurLiftExtension_eq (t, scaledBand t) (chart_energy_inBox ht (scaledBand_mem ht))]

theorem clusterVector_kernel {t : Momentum} (ht : t ∈ chart) :
    finiteSchur t (scaledBand t) (chart_closed_bounds ht)
      (chart_energy_inBox ht (scaledBand_mem ht)).2 (clusterVector t) = 0 := by
  rw [finiteSchur_eq_bandOperator]
  unfold scaledBand clusterVector
  exact actualCornerData.bandVector_kernel perturbationData t ht

theorem fiberVector_analytic : AnalyticOnNhd ℂ fiberVector chart := by
  intro t ht
  have hp : AnalyticAt ℂ (fun s => (s, scaledBand s)) t :=
    analyticAt_id.prod (scaledBand_analytic t ht)
  have hL := AnalyticAt.comp (f := fun s : Momentum => (s, scaledBand s))
    (analyticAt_schurLiftExtension (t, scaledBand t)
      (chart_energy_inBox ht (scaledBand_mem ht))) hp
  have hc : AnalyticAt ℂ (fun s => (clusterVector s).val) t :=
    (clusterSpace.subtypeL.analyticAt (clusterVector t)).comp (clusterVector_analytic t ht)
  exact (hL.contDiffAt.clm_apply hc.contDiffAt).analyticAt

theorem clusterProjection_fiberVector {t : Momentum} (ht : t ∈ chart) :
    clusterProjection (fiberVector t) = (clusterVector t).val := by
  rw [fiberVector_eq ht, clusterProjection_schurLift]
  exact (mem_clusterSpace_iff _).mp (clusterVector t).property

theorem fiberVector_ne_zero {t : Momentum} (ht : t ∈ chart) : fiberVector t ≠ 0 := by
  intro h
  have hp := clusterProjection_fiberVector ht
  rw [h, map_zero] at hp
  exact clusterVector_ne_zero t (Subtype.ext hp.symm)

theorem fiberVector_graph {t : Momentum} (ht : t ∈ chart) :
    (fiberVector t, 0) ∈ (materialFiber (scaledMomentum t)
      (totalEnergy (scaledBand t)) backgroundAmplitude).graph := by
  have hb := chart_energy_inBox ht (scaledBand_mem ht)
  have hfinite := clusterVector_kernel ht
  have heff : effectiveSchur t (scaledBand t) hb.1 hb.2 (clusterVector t).val = 0 :=
    congrArg Subtype.val hfinite
  rw [LinearPMap.mem_graph_iff]
  refine ⟨⟨schurLift t (scaledBand t) hb.1 hb.2 (clusterVector t).val,
    schurLift_mem_domain t (scaledBand t) hb.1 hb.2 (clusterVector t).val⟩, ?_, ?_⟩
  · exact (fiberVector_eq ht).symm
  · exact schur_kernel_lifts t (scaledBand t) hb.1 hb.2 (clusterVector t).val heff

/-- All aliases, including the longitudinal complementary sector, are included. -/
theorem fiberVector_fourier_l1 {t : Momentum} (ht : t ∈ chart) :
    Summable (fun ν => ‖fiberVector t ν‖) ∧ ∑' ν, ‖fiberVector t ν‖ ≤ 18 := by
  have hb := chart_energy_inBox ht (scaledBand_mem ht)
  obtain ⟨u, hu, heq⟩ :=
    (LinearPMap.mem_graph_iff _).mp (fiberVector_graph ht)
  have hs := FiberL1.kernel_summable_norm t (scaledBand t) hb.1 hb.2 u heq
  have hn := FiberL1.kernel_fourier_l1_le t (scaledBand t) hb.1 hb.2 u heq
  rw [hu] at hs hn
  rw [clusterProjection_fiberVector ht] at hn
  have hc := clusterVector_norm_le ht
  exact ⟨hs, hn.trans (by change 9 * ‖clusterVector t‖ ≤ 18; linarith)⟩

end Maxwell.Continuum.PeriodicBand
