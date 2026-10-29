import Maxwell.Continuum.PeriodicBandPoleFactors

/-! The physical-energy residue is the actual operator-norm limit of the
full infinite-fiber resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge Metric Set Filter
open scoped Topology

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot

theorem energyDisk_mem_nhds_band {t : Momentum} (ht : t ∈ chart) :
    energyDisk ∈ 𝓝 (scaledBand t) := by
  apply closedBall_mem_nhds_of_mem
  rw [mem_ball, dist_eq_norm]
  exact (scaledBand_center_bound ht).trans_lt (by norm_num)

theorem scaled_fullResolvent_pole_formula {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    ((backgroundAmplitude : ℂ) * (e - scaledBand t)) • fullResolventExtension (t, e) =
      fullPoleResidue t + ((backgroundAmplitude : ℂ) * (e - scaledBand t)) •
        fullSeparatedResolvent t e := by
  have hρ : (backgroundAmplitude : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr backgroundAmplitude_pos.ne'
  rw [fullResolvent_pole_formula ht he hne, smul_add, smul_smul,
    mul_inv_cancel₀ (mul_ne_zero hρ (sub_ne_zero.mpr hne)), one_smul]

theorem tendsto_scaled_fullResolvent {t : Momentum} (ht : t ∈ chart) :
    Tendsto (fun e => ((backgroundAmplitude : ℂ) * (e - scaledBand t)) •
      fullResolventExtension (t, e)) (𝓝[≠] scaledBand t) (𝓝 (fullPoleResidue t)) := by
  have hs := (analyticAt_fullSeparatedResolvent ht (scaledBand_mem ht)).continuousAt
  have hz : Tendsto (fun e : ℂ => (backgroundAmplitude : ℂ) * (e - scaledBand t))
      (𝓝 (scaledBand t)) (𝓝 (0 : ℂ)) := by
    have hid : Tendsto (fun e : ℂ => e - scaledBand t)
        (𝓝 (scaledBand t)) (𝓝 (0 : ℂ)) := by
      have hi : Tendsto (fun e : ℂ => e) (𝓝 (scaledBand t)) (𝓝 (scaledBand t)) := tendsto_id
      simpa only [sub_self, id_eq] using hi.sub_const (scaledBand t)
    have hcρ : Tendsto (fun _ : ℂ => (backgroundAmplitude : ℂ))
        (𝓝 (scaledBand t)) (𝓝 (backgroundAmplitude : ℂ)) := tendsto_const_nhds
    simpa only [mul_zero] using hcρ.mul hid
  have hc : Tendsto (fun _ : ℂ => fullPoleResidue t)
      (𝓝 (scaledBand t)) (𝓝 (fullPoleResidue t)) := tendsto_const_nhds
  have hl : Tendsto (fun e => fullPoleResidue t +
      ((backgroundAmplitude : ℂ) * (e - scaledBand t)) • fullSeparatedResolvent t e)
      (𝓝 (scaledBand t)) (𝓝 (fullPoleResidue t)) := by
    have hsum := hc.add (hz.smul hs)
    change Tendsto _ _ (𝓝 (fullPoleResidue t + (0 : ℂ) •
      fullSeparatedResolvent t (scaledBand t))) at hsum
    have hzero : (0 : ℂ) • fullSeparatedResolvent t (scaledBand t) = 0 := by
      apply ContinuousLinearMap.ext
      intro u
      change (0 : ℂ) • fullSeparatedResolvent t (scaledBand t) u = 0
      exact zero_smul ℂ (fullSeparatedResolvent t (scaledBand t) u)
    rw [hzero, add_zero] at hsum
    exact hsum
  have hev : ∀ᶠ e in 𝓝 (scaledBand t), e ∈ energyDisk := energyDisk_mem_nhds_band ht
  apply (hl.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,
    hev.filter_mono nhdsWithin_le_nhds] with e hne he
  exact (scaled_fullResolvent_pole_formula ht he hne).symm

end Maxwell.Continuum.PeriodicBand
