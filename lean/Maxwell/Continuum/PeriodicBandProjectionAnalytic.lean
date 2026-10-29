import Maxwell.Continuum.PeriodicBandProjectionBilinear
import Maxwell.Continuum.FiberNormalizationNormalized

/-! The actual spectral projection equals the bilinear rank-one map of
the constructed normalized Fourier eigenvector. This gives joint
momentum holomorphy and a uniform operator-norm bound on the full chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic FiberNormalization CornerBridge PeriodicPerturbation
open scoped ContDiff Topology

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot
  scaledBand clusterVector fiberVector normalizedFiberVector

def bilinearProjection (t : Momentum) : FiberMap :=
  (bilinear (normalizedFiberVector t)).smulRight (normalizedFiberVector t)

theorem fullSpectralProjection_eq_bilinearProjection {t : Momentum} (ht : t ∈ chart) :
    fullSpectralProjection t = bilinearProjection t := by
  apply ContinuousLinearMap.ext
  intro u
  exact fullSpectralProjection_eq_bilinear ht (normalizedFiberVector t)
    ((mem_physicalKernel_iff t _).mpr (normalizedFiberVector_graph ht))
    (normalizedFiberVector_bilinear ht) u

theorem bilinearProjection_analytic : AnalyticOnNhd ℂ bilinearProjection chart := by
  intro t ht
  have hw := (normalizedFiberVector_analytic t ht).contDiffAt (n := ω)
  have hB : ContDiff ℂ ω (bilinear : FiberSpace →L[ℂ] FiberSpace →L[ℂ] ℂ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := FiberSpace) (F := FiberSpace →L[ℂ] ℂ) bilinear
  have hb := hB.contDiffAt.comp t hw
  have hS : ContDiff ℂ ω (ContinuousLinearMap.smulRightL ℂ FiberSpace FiberSpace) :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := FiberSpace →L[ℂ] ℂ)
      (F := FiberSpace →L[ℂ] FiberMap) (ContinuousLinearMap.smulRightL ℂ FiberSpace FiberSpace)
  exact ((hS.contDiffAt.comp t hb).clm_apply hw).analyticAt

/-- Joint momentum analyticity of the genuine full-fiber spectral projection. -/
theorem fullSpectralProjection_analytic : AnalyticOnNhd ℂ fullSpectralProjection chart := by
  intro t ht
  apply (bilinearProjection_analytic t ht).congr
  filter_upwards [chart_isOpen.mem_nhds ht] with s hs
  exact (fullSpectralProjection_eq_bilinearProjection hs).symm

theorem normalizedFiberVector_norm_le {t : Momentum} (ht : t ∈ chart) :
    ‖normalizedFiberVector t‖ ≤ 9 / 5 := by
  have hn : ‖fiberVector t‖ ≤ 6 / 5 := by
    have h := norm_add_le (fiberVector t - topState.val) topState.val
    have htop : ‖topState.val‖ = 1 := topState_norm
    rw [sub_add_cancel, htop] at h
    linarith [fiberVector_sub_top_bound ht]
  have hm := multiplier_norm_le topState.val (fiberVector t) topState_star topState_norm
    (fiberVector_sub_top_bound ht)
  unfold normalizedFiberVector
  rw [FiberNormalization.normalize, norm_smul]
  calc
    _ ≤ (3 / 2) * (6 / 5) := mul_le_mul hm hn (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem fullSpectralProjection_norm_le {t : Momentum} (ht : t ∈ chart) :
    ‖fullSpectralProjection t‖ ≤ 81 / 25 := by
  rw [fullSpectralProjection_eq_bilinearProjection ht]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖(bilinear (normalizedFiberVector t) u) • normalizedFiberVector t‖ ≤ _
  rw [norm_smul]
  have hB := bilinear_norm_le (normalizedFiberVector t) u
  have hn := normalizedFiberVector_norm_le ht
  calc
    _ ≤ ((9 / 5) * ‖u‖) * (9 / 5) := mul_le_mul
      (hB.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg u))) hn (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Maxwell.Continuum.PeriodicBand
