import Maxwell.Continuum.PeriodicBandResolventAlgebra

/-! The separated resolvent satisfies both resolvent identities through
the selected band itself. Energy analyticity supplies the value at the
removable singularity; no inverse hypothesis is made there. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic Metric Set Filter
open scoped Topology

theorem fiberMap_smul_mul (c : ℂ) (A B : FiberMap) : (c • A) * B = c • (A * B) := rfl

theorem fiberMap_mul_smul (c : ℂ) (A B : FiberMap) : A * (c • B) = c • (A * B) := by
  apply ContinuousLinearMap.ext
  intro f
  exact A.map_smul c (B f)

theorem fullSeparated_product {t : Momentum} (ht : t ∈ chart) {e f : ℂ}
    (he : e ∈ energyDisk) (hf : f ∈ energyDisk)
    (hne : e ≠ scaledBand t) (hnf : f ≠ scaledBand t) :
    fullSeparatedResolvent t e * fullSeparatedResolvent t f =
      (fullResolventExtension (t, e) * fullResolventExtension (t, f)) * fullBandComplement t := by
  have hcomm : fullBandComplement t * fullResolventExtension (t, f) =
      fullResolventExtension (t, f) * fullBandComplement t :=
    (fullSeparated_eq_complement_resolvent ht hf hnf).symm.trans
      (fullSeparated_eq_resolvent_complement ht hf hnf)
  rw [fullSeparated_eq_resolvent_complement ht he hne,
    fullSeparated_eq_complement_resolvent ht hf hnf]
  calc
    _ = fullResolventExtension (t, e) * (fullBandComplement t * fullBandComplement t) *
        fullResolventExtension (t, f) := by simp only [mul_assoc]
    _ = fullResolventExtension (t, e) * fullBandComplement t * fullResolventExtension (t, f) := by
      rw [fullBandComplement_idempotent ht]
    _ = _ := by rw [mul_assoc, hcomm, ← mul_assoc]

theorem fullSeparated_identity_away {t : Momentum} (ht : t ∈ chart) {e f : ℂ}
    (he : e ∈ energyDisk) (hf : f ∈ energyDisk)
    (hne : e ≠ scaledBand t) (hnf : f ≠ scaledBand t) :
    fullSeparatedResolvent t e - fullSeparatedResolvent t f =
      ((backgroundAmplitude : ℂ) * (e - f)) •
        (fullSeparatedResolvent t e * fullSeparatedResolvent t f) := by
  have hsub : fullSeparatedResolvent t e - fullSeparatedResolvent t f =
      (fullResolventExtension (t, e) - fullResolventExtension (t, f)) * fullBandComplement t := by
    rw [sub_mul, ← fullSeparated_eq_resolvent_complement ht he hne,
      ← fullSeparated_eq_resolvent_complement ht hf hnf]
  rw [hsub, fullResolvent_identity ht he hf hne hnf, fiberMap_smul_mul,
    ← fullSeparated_product ht he hf hne hnf]

theorem fullSeparated_identity_rev_away {t : Momentum} (ht : t ∈ chart) {e f : ℂ}
    (he : e ∈ energyDisk) (hf : f ∈ energyDisk)
    (hne : e ≠ scaledBand t) (hnf : f ≠ scaledBand t) :
    fullSeparatedResolvent t e - fullSeparatedResolvent t f =
      ((backgroundAmplitude : ℂ) * (e - f)) •
        (fullSeparatedResolvent t f * fullSeparatedResolvent t e) := by
  have hsub : fullSeparatedResolvent t e - fullSeparatedResolvent t f =
      (fullResolventExtension (t, e) - fullResolventExtension (t, f)) * fullBandComplement t := by
    rw [sub_mul, ← fullSeparated_eq_resolvent_complement ht he hne,
      ← fullSeparated_eq_resolvent_complement ht hf hnf]
  rw [hsub, fullResolvent_identity_rev ht he hf hne hnf, fiberMap_smul_mul,
    ← fullSeparated_product ht hf he hnf hne]

theorem eq_at_band_of_away {F : Type*} [TopologicalSpace F] [T2Space F]
    {t : Momentum} (ht : t ∈ chart) (f g : ℂ → F)
    (hf : ContinuousAt f (scaledBand t)) (hg : ContinuousAt g (scaledBand t))
    (heq : ∀ e ∈ energyDisk, e ≠ scaledBand t → f e = g e) :
    f (scaledBand t) = g (scaledBand t) := by
  have hev : ∀ᶠ e in 𝓝 (scaledBand t), e ∈ energyDisk := energyDisk_mem_nhds_band ht
  have hl : Tendsto f (𝓝[≠] scaledBand t) (𝓝 (f (scaledBand t))) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto g (𝓝[≠] scaledBand t) (𝓝 (g (scaledBand t))) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique hl (hr.congr' ?_)
  filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds] with e hne he
  exact (heq e he hne).symm

theorem fullSeparated_identity {t : Momentum} (ht : t ∈ chart) {e f : ℂ}
    (he : e ∈ energyDisk) (hf : f ∈ energyDisk) (hnf : f ≠ scaledBand t) :
    fullSeparatedResolvent t e - fullSeparatedResolvent t f =
      ((backgroundAmplitude : ℂ) * (e - f)) •
        (fullSeparatedResolvent t e * fullSeparatedResolvent t f) := by
  by_cases hne : e = scaledBand t
  · subst e
    have hS := (analyticAt_fullSeparatedResolvent ht (scaledBand_mem ht)).continuousAt
    apply eq_at_band_of_away ht
      (fun e => fullSeparatedResolvent t e - fullSeparatedResolvent t f)
      (fun e => ((backgroundAmplitude : ℂ) * (e - f)) •
        (fullSeparatedResolvent t e * fullSeparatedResolvent t f))
      (hS.sub continuousAt_const)
      ((continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).smul
        (hS.mul continuousAt_const))
    exact fun e he hne => fullSeparated_identity_away ht he hf hne hnf
  · exact fullSeparated_identity_away ht he hf hne hnf

theorem fullSeparated_identity_rev {t : Momentum} (ht : t ∈ chart) {e f : ℂ}
    (he : e ∈ energyDisk) (hf : f ∈ energyDisk) (hnf : f ≠ scaledBand t) :
    fullSeparatedResolvent t e - fullSeparatedResolvent t f =
      ((backgroundAmplitude : ℂ) * (e - f)) •
        (fullSeparatedResolvent t f * fullSeparatedResolvent t e) := by
  by_cases hne : e = scaledBand t
  · subst e
    have hS := (analyticAt_fullSeparatedResolvent ht (scaledBand_mem ht)).continuousAt
    apply eq_at_band_of_away ht
      (fun e => fullSeparatedResolvent t e - fullSeparatedResolvent t f)
      (fun e => ((backgroundAmplitude : ℂ) * (e - f)) •
        (fullSeparatedResolvent t f * fullSeparatedResolvent t e))
      (hS.sub continuousAt_const)
      ((continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).smul
        (continuousAt_const.mul hS))
    exact fun e he hne => fullSeparated_identity_rev_away ht he hf hne hnf
  · exact fullSeparated_identity_rev_away ht he hf hne hnf

end Maxwell.Continuum.PeriodicBand
