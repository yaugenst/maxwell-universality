import Maxwell.Continuum.FiberNormalizationReal

/-! An actual holomorphic normalized continuum Bloch eigenvector, with
every alias included and a uniform absolute Fourier bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiberNormalization

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge PeriodicBand

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot
  scaledBand clusterVector fiberVector

def normalizedFiberVector (t : Momentum) : FiberSpace := normalize (fiberVector t)

theorem normalizedFiberVector_analytic : AnalyticOnNhd ℂ normalizedFiberVector chart := by
  intro t ht
  exact analyticAt_normalize (fiberVector_analytic t ht) (fiberVector_bilinear_bound ht)

theorem normalizedFiberVector_bilinear {t : Momentum} (ht : t ∈ chart) :
    bilinear (normalizedFiberVector t) (normalizedFiberVector t) = 1 :=
  bilinear_normalize _ (fiberVector_bilinear_ne_zero ht)

theorem normalizedFiberVector_ne_zero {t : Momentum} (ht : t ∈ chart) :
    normalizedFiberVector t ≠ 0 := by
  exact smul_ne_zero (multiplier_ne_zero _ (fiberVector_bilinear_ne_zero ht))
    (fiberVector_ne_zero ht)

theorem normalizedFiberVector_graph {t : Momentum} (ht : t ∈ chart) :
    (normalizedFiberVector t, 0) ∈ (materialFiber (scaledMomentum t)
      (totalEnergy (scaledBand t)) backgroundAmplitude).graph := by
  have h := (materialFiber (scaledMomentum t)
    (totalEnergy (scaledBand t)) backgroundAmplitude).graph.smul_mem
      (multiplier (fiberVector t)) (fiberVector_graph ht)
  simpa only [Prod.smul_mk, smul_zero, normalizedFiberVector, normalize] using h

theorem normalizedFiberVector_norm_real (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    ‖normalizedFiberVector (realMomentum t)‖ = 1 :=
  normalize_real_norm _ (fiberVector_real t ht) (fiberVector_ne_zero ht)

theorem normalizedFiberVector_fourier_norm (t : Momentum) (ν : Alias) :
    ‖normalizedFiberVector t ν‖ = ‖multiplier (fiberVector t)‖ * ‖fiberVector t ν‖ := by
  change ‖multiplier (fiberVector t) • fiberVector t ν‖ = _
  exact norm_smul _ _

theorem normalizedFiberVector_fourier_l1_sharp {t : Momentum} (ht : t ∈ chart) :
    Summable (fun ν => ‖normalizedFiberVector t ν‖) ∧
      ∑' ν, ‖normalizedFiberVector t ν‖ ≤ 27 := by
  have hv := fiberVector_fourier_l1 ht
  have hm := multiplier_norm_le topState.val (fiberVector t) topState_star topState_norm
    (fiberVector_sub_top_bound ht)
  simp only [normalizedFiberVector_fourier_norm]
  refine ⟨hv.1.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have h := mul_le_mul hm hv.2 (tsum_nonneg fun ν => norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3/2)
  nlinarith

theorem normalizedFiberVector_fourier_l1 {t : Momentum} (ht : t ∈ chart) :
    Summable (fun ν => ‖normalizedFiberVector t ν‖) ∧
      ∑' ν, ‖normalizedFiberVector t ν‖ ≤ 32 :=
  ⟨(normalizedFiberVector_fourier_l1_sharp ht).1,
    (normalizedFiberVector_fourier_l1_sharp ht).2.trans (by norm_num)⟩

#print axioms normalizedFiberVector_analytic
#print axioms normalizedFiberVector_bilinear
#print axioms normalizedFiberVector_ne_zero
#print axioms normalizedFiberVector_graph
#print axioms normalizedFiberVector_norm_real
#print axioms normalizedFiberVector_fourier_l1

end Maxwell.Continuum.FiberNormalization
