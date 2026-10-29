import Maxwell.Continuum.PeriodicBandPoleLimit
import Maxwell.Continuum.FreeFiberEnergyShift

/-! The physical-energy pole residue yields a genuine bounded spectral
projection on the full infinite alias Hilbert space. Its range is exactly
the actual maximal-domain band eigenspace and has dimension one. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge Metric Set Filter
open scoped Topology

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot

def physicalKernel (t : Momentum) : Submodule ℂ FiberSpace :=
  (ActualKernel t (scaledBand t)).map
    (materialFiber (scaledMomentum t) (totalEnergy (scaledBand t)) backgroundAmplitude).domain.subtype

theorem mem_physicalKernel_iff (t : Momentum) (u : FiberSpace) :
    u ∈ physicalKernel t ↔
      (u, 0) ∈ (materialFiber (scaledMomentum t) (physicalBand t) backgroundAmplitude).graph := by
  rw [physicalKernel, Submodule.mem_map, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx, hxu⟩
    exact ⟨x, hxu, hx⟩
  · rintro ⟨x, hx, hAx⟩
    exact ⟨x, hAx, hx⟩

theorem physicalKernel_finrank {t : Momentum} (ht : t ∈ chart) :
    Module.finrank ℂ (physicalKernel t) = 1 := by
  rw [physicalKernel, Submodule.finrank_map_subtype_eq]
  exact actual_band_kernel_finrank ht

theorem fullPoleResidue_mem_kernel {t : Momentum} (ht : t ∈ chart) (f : FiberSpace) :
    fullPoleResidue t f ∈ physicalKernel t := by
  let b := scaledBand t
  have hb := chart_energy_inBox ht (scaledBand_mem ht)
  let y : clusterSpace := actualCornerData.poleResidue perturbationData t
    (adjustedSourceExtension (t, b) f)
  have hyker : RankOneBand.operator finiteK (perturbation (t, b)) b y = 0 := by
    have hy : y ∈ (actualCornerData.poleResidue perturbationData t).range :=
      ⟨adjustedSourceExtension (t, b) f, rfl⟩
    rw [actualCornerData.poleResidue_range perturbationData actualPerturbation_analytic t ht] at hy
    exact hy
  have hfy : finiteSchur t b hb.1 hb.2 y = 0 := by
    rw [finiteSchur_eq_bandOperator]
    exact hyker
  have hyeff : effectiveSchur t b hb.1 hb.2 y.val = 0 := congrArg Subtype.val hfy
  have hval : fullPoleResidue t f = schurLift t b hb.1 hb.2 y.val := by
    have hval0 : fullPoleResidue t f = schurLiftExtension (t, b) y.val := by
      simp only [fullPoleResidue, fullPoleNumerator, liftFiniteOperator,
        ContinuousLinearMap.comp_apply, RankOneBand.Data.poleResidue, y, b]
      rfl
    exact hval0.trans (congrArg (fun A : FiberMap => A y.val)
      (schurLiftExtension_eq (t, b) hb))
  rw [mem_physicalKernel_iff, hval, LinearPMap.mem_graph_iff]
  exact ⟨⟨schurLift t b hb.1 hb.2 y.val, schurLift_mem_domain t b hb.1 hb.2 y.val⟩,
    rfl, schur_kernel_lifts t b hb.1 hb.2 y.val hyeff⟩

/-- The minus sign is forced by the `A-E` resolvent convention. -/
theorem fullPoleResidue_on_kernel {t : Momentum} (ht : t ∈ chart) (u : FiberSpace)
    (hu : u ∈ physicalKernel t) : fullPoleResidue t u = -u := by
  have hu' := (mem_physicalKernel_iff t u).mp hu
  have hlim := ((ContinuousLinearMap.apply ℂ FiberSpace u).continuous.tendsto (fullPoleResidue t)).comp
    (tendsto_scaled_fullResolvent ht)
  change Tendsto (fun e => ((backgroundAmplitude : ℂ) * (e - scaledBand t)) •
      fullResolventExtension (t, e) u) (𝓝[≠] scaledBand t) (𝓝 (fullPoleResidue t u)) at hlim
  have hev : ∀ᶠ e in 𝓝 (scaledBand t), e ∈ energyDisk := energyDisk_mem_nhds_band ht
  have heq : ∀ᶠ e in 𝓝[≠] scaledBand t,
      ((backgroundAmplitude : ℂ) * (e - scaledBand t)) • fullResolventExtension (t, e) u = -u := by
    filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds] with e hne he
    have hn : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50 := by
      have hd : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 100 := by
        simpa only [energyDisk, mem_closedBall, dist_eq_norm] using he
      linarith
    have hR := inverse_scaled_on_kernel (scaledMomentum t) (totalEnergy e)
      (physicalBand t) backgroundAmplitude (inverseAwayFromBand ht hn hne) u hu'
    rw [← fullResolventExtension_eq_inverseAwayFromBand ht hn hne] at hR
    change (totalEnergy e - totalEnergy (scaledBand t)) • fullResolventExtension (t, e) u = -u at hR
    rw [totalEnergy_sub] at hR
    exact hR
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq))

def fullSpectralProjection (t : Momentum) : FiberMap := -fullPoleResidue t

theorem fullSpectralProjection_on_kernel {t : Momentum} (ht : t ∈ chart) (u : FiberSpace)
    (hu : u ∈ physicalKernel t) : fullSpectralProjection t u = u := by
  change -(fullPoleResidue t u) = u
  rw [fullPoleResidue_on_kernel ht u hu, neg_neg]

theorem fullSpectralProjection_range {t : Momentum} (ht : t ∈ chart) :
    (fullSpectralProjection t).range = physicalKernel t := by
  ext u
  constructor
  · rintro ⟨f, rfl⟩
    exact (physicalKernel t).neg_mem (fullPoleResidue_mem_kernel ht f)
  · intro hu
    exact ⟨u, fullSpectralProjection_on_kernel ht u hu⟩

theorem fullSpectralProjection_idempotent {t : Momentum} (ht : t ∈ chart) :
    fullSpectralProjection t * fullSpectralProjection t = fullSpectralProjection t := by
  apply ContinuousLinearMap.ext
  intro u
  apply fullSpectralProjection_on_kernel ht
  rw [← fullSpectralProjection_range ht]
  exact ⟨u, rfl⟩

theorem fullSpectralProjection_finrank {t : Momentum} (ht : t ∈ chart) :
    Module.finrank ℂ (fullSpectralProjection t).range = 1 := by
  rw [fullSpectralProjection_range ht]
  exact physicalKernel_finrank ht

end Maxwell.Continuum.PeriodicBand
