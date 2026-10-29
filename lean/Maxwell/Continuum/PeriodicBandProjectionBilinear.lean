import Maxwell.Continuum.FreeFiberBilinear

/-! Bilinear symmetry of the actual physical residue and projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic FiberNormalization Metric Set Filter
open scoped Topology

theorem fullPoleResidue_bilinear_symmetric {t : Momentum} (ht : t ∈ chart) (u v : FiberSpace) :
    bilinear (fullPoleResidue t u) v = bilinear u (fullPoleResidue t v) := by
  have hu := ((ContinuousLinearMap.apply ℂ FiberSpace u).continuous.tendsto (fullPoleResidue t)).comp
    (tendsto_scaled_fullResolvent ht)
  have hv := ((ContinuousLinearMap.apply ℂ FiberSpace v).continuous.tendsto (fullPoleResidue t)).comp
    (tendsto_scaled_fullResolvent ht)
  have hl := ((bilinear.flip v).continuous.tendsto (fullPoleResidue t u)).comp hu
  have hr := ((bilinear u).continuous.tendsto (fullPoleResidue t v)).comp hv
  have hev : ∀ᶠ e in 𝓝 (scaledBand t), e ∈ energyDisk := energyDisk_mem_nhds_band ht
  have heq : (fun e => bilinear
      (((backgroundAmplitude : ℂ) * (e - scaledBand t)) • fullResolventExtension (t, e) u) v)
      =ᶠ[𝓝[≠] scaledBand t]
      (fun e => bilinear u
        (((backgroundAmplitude : ℂ) * (e - scaledBand t)) • fullResolventExtension (t, e) v)) := by
    filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds] with e hne he
    have hn : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50 := by
      have hd : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 100 := by
        simpa only [energyDisk, mem_closedBall, dist_eq_norm] using he
      linarith
    have h := inverse_bilinear_symmetric (scaledMomentum t) (totalEnergy e)
      backgroundAmplitude (inverseAwayFromBand ht hn hne) u v
    rw [← fullResolventExtension_eq_inverseAwayFromBand ht hn hne] at h
    simp only [map_smul, smul_apply, smul_eq_mul]
    exact congrArg (fun z : ℂ => ((backgroundAmplitude : ℂ) * (e - scaledBand t)) * z) h
  exact tendsto_nhds_unique hl (hr.congr' (Filter.EventuallyEq.symm heq))

theorem fullSpectralProjection_bilinear_symmetric {t : Momentum} (ht : t ∈ chart)
    (u v : FiberSpace) :
    bilinear (fullSpectralProjection t u) v = bilinear u (fullSpectralProjection t v) := by
  change bilinear (-(fullPoleResidue t u)) v = bilinear u (-(fullPoleResidue t v))
  simp only [map_neg, neg_apply]
  rw [fullPoleResidue_bilinear_symmetric ht]

theorem fullSpectralProjection_eq_bilinear {t : Momentum} (ht : t ∈ chart)
    (w : FiberSpace) (hw : w ∈ physicalKernel t) (hunit : bilinear w w = 1) (u : FiberSpace) :
    fullSpectralProjection t u = (bilinear w u) • w := by
  have hw0 : w ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hunit
    exact zero_ne_one hunit
  have hspan : physicalKernel t = ℂ ∙ w :=
    eq_span_singleton_of_mem_of_finrank_eq_one (physicalKernel_finrank ht) hw hw0
  have hPu : fullSpectralProjection t u ∈ physicalKernel t := by
    rw [← fullSpectralProjection_range ht]
    exact ⟨u, rfl⟩
  rw [hspan] at hPu
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hPu
  have h := fullSpectralProjection_bilinear_symmetric ht w u
  rw [fullSpectralProjection_on_kernel ht w hw, ← ha, map_smul, hunit] at h
  change bilinear w u = a * 1 at h
  rw [mul_one] at h
  exact ha.symm.trans (congrArg (fun z : ℂ => z • w) h.symm)

end Maxwell.Continuum.PeriodicBand
