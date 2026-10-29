import Maxwell.Continuum.CellBandFourierReversal

/-! Schwarz conjugation and alias reversal of the actual normalized band.
The selected coefficient gauge fixes the signs without a phase assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge
  PeriodicBand FiberNormalization

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot
  scaledBand clusterVector fiberVector normalizedFiberVector

theorem chart_star {t : Momentum} (ht : t ∈ chart) : star t ∈ chart := by
  intro j
  change ‖star (t j)‖ < _
  rw [norm_star]
  exact ht j

theorem energyDisk_star {e : ℂ} (he : e ∈ energyDisk) : star e ∈ energyDisk := by
  simp only [energyDisk, Metric.mem_closedBall, dist_eq_norm] at he ⊢
  have h : star e - (Corner.lambdaStar : ℂ) = star (e - (Corner.lambdaStar : ℂ)) := by
    simp only [star_sub, Complex.star_def, Complex.conj_ofReal]
  rw [h, norm_star]
  exact he

theorem scaledMomentum_star (t : Momentum) : star (scaledMomentum t) = scaledMomentum (star t) := by
  funext j
  simp [scaledMomentum, mul_comm]

theorem totalEnergy_star (e : ℂ) : star (totalEnergy e) = totalEnergy (star e) := by
  simp [totalEnergy, mul_comm]

theorem scaledMomentum_neg (t : Momentum) : -scaledMomentum t = scaledMomentum (-t) := by
  funext j
  simp [scaledMomentum]

theorem scaledBand_schwarz {t : Momentum} (ht : t ∈ chart) :
    scaledBand (star t) = star (scaledBand t) := by
  have hg := material_graph_star _ _ backgroundAmplitude _ _ (fiberVector_graph ht)
  rw [star_zero, scaledMomentum_star, totalEnergy_star] at hg
  have hn : star (fiberVector t) ≠ 0 := by
    intro h
    exact fiberVector_ne_zero ht (by simpa only [star_star, star_zero] using congrArg star h)
  exact ((actual_nonzero_iff_scaledBand (chart_star ht)
    (energyDisk_star (scaledBand_mem ht))).mp ⟨_, hn, hg⟩).symm

theorem fiberVector_unique_gauge {t : Momentum} (ht : t ∈ chart) (v : FiberSpace)
    (hv : (v,0) ∈ (materialFiber (scaledMomentum t)
      (totalEnergy (scaledBand t)) backgroundAmplitude).graph)
    (hg : inner ℂ topState.val v = 1) : v = fiberVector t := by
  obtain ⟨x, hx, hx0⟩ := (LinearPMap.mem_graph_iff _).mp (fiberVector_graph ht)
  obtain ⟨y, hy, hy0⟩ := (LinearPMap.mem_graph_iff _).mp hv
  let xk : ActualKernel t (scaledBand t) := ⟨x, hx0⟩
  let yk : ActualKernel t (scaledBand t) := ⟨y, hy0⟩
  have hxk : xk ≠ 0 := by
    intro h
    have hz := congrArg (fun z : ActualKernel t (scaledBand t) => z.val.val) h
    change x.val = 0 at hz
    rw [hx] at hz
    exact fiberVector_ne_zero ht hz
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one (actual_band_kernel_finrank ht) hxk yk
  have hav := congrArg (fun z : ActualKernel t (scaledBand t) => z.val.val) ha
  change a • x.val = y.val at hav
  rw [hx, hy] at hav
  have hc := congrArg (fun w : FiberSpace => inner ℂ topState.val w) hav
  rw [inner_smul_right, fiberVector_gauge ht, hg, mul_one] at hc
  simpa only [hc, one_smul] using hav.symm

theorem fiberVector_schwarz {t : Momentum} (ht : t ∈ chart) :
    fiberVector (star t) = star (fiberVector t) := by
  apply Eq.symm
  apply fiberVector_unique_gauge (chart_star ht)
  · have hg := material_graph_star _ _ backgroundAmplitude _ _ (fiberVector_graph ht)
    rw [star_zero, scaledMomentum_star, totalEnergy_star, ← scaledBand_schwarz ht] at hg
    exact hg
  · exact fiberVector_star_gauge ht

theorem fiberVector_reversal {t : Momentum} (ht : t ∈ chart) :
    reversal (fiberVector t) = -fiberVector (-t) := by
  have heq : -reversal (fiberVector t) = fiberVector (-t) := by
    apply fiberVector_unique_gauge (chart_neg ht)
    · have h := material_graph_reverse _ _ backgroundAmplitude _ _ (fiberVector_graph ht)
      rw [map_zero, scaledMomentum_neg, ← scaledBand_neg ht] at h
      simpa only [Prod.neg_mk, neg_zero] using
        (materialFiber (scaledMomentum (-t))
          (totalEnergy (scaledBand (-t))) backgroundAmplitude).graph.neg_mem h
    · rw [inner_neg_right, ← reversal_inner, reversal_topState, inner_neg_left,
        fiberVector_gauge ht, neg_neg]
  exact neg_eq_iff_eq_neg.mp heq

theorem reversal_star (v : FiberSpace) : reversal (star v) = star (reversal v) := by
  apply lp.ext
  funext ν
  simp only [reversal_apply, fiber_star_apply]

theorem bilinear_reversal (u v : FiberSpace) : bilinear (reversal u) (reversal v) = bilinear u v := by
  rw [bilinear_apply, ← reversal_star, reversal.inner_map_map, bilinear_apply]

theorem bilinear_star (u v : FiberSpace) : bilinear (star u) (star v) = star (bilinear u v) := by
  simp only [bilinear_apply]
  exact fiber_inner_star (star u) v

theorem sqrt_star_near_one (z : ℂ) (hz : ‖z-1‖ ≤ 11/25) :
    Complex.sqrt (star z) = star (Complex.sqrt z) := by
  have ha := Complex.slitPlane_arg_ne_pi (Or.inl (near_one_re_pos z hz))
  simpa only [Complex.sqrt, Complex.star_def, map_inv₀, map_ofNat] using
    Complex.conj_cpow z (2⁻¹ : ℂ) ha

theorem normalizedFiberVector_schwarz {t : Momentum} (ht : t ∈ chart) :
    normalizedFiberVector (star t) = star (normalizedFiberVector t) := by
  simp only [normalizedFiberVector, fiberVector_schwarz ht, FiberNormalization.normalize,
    multiplier, bilinear_star, star_smul]
  rw [sqrt_star_near_one _ (fiberVector_bilinear_bound ht), star_inv₀]

theorem normalizedFiberVector_reversal {t : Momentum} (ht : t ∈ chart) :
    reversal (normalizedFiberVector t) = -normalizedFiberVector (-t) := by
  have hb : bilinear (fiberVector (-t)) (fiberVector (-t)) =
      bilinear (fiberVector t) (fiberVector t) := by
    have h := bilinear_reversal (fiberVector t) (fiberVector t)
    rw [fiberVector_reversal ht] at h
    simpa only [map_neg, neg_apply, neg_neg] using h
  simp only [normalizedFiberVector, FiberNormalization.normalize, map_smul,
    fiberVector_reversal ht, smul_neg, multiplier, hb]

theorem normalizedFiberVector_imaginary {t : Momentum} (ht : t ∈ chart)
    (hi : star t = -t) : reversal (star (normalizedFiberVector t)) = -normalizedFiberVector t := by
  rw [← normalizedFiberVector_schwarz ht, hi, normalizedFiberVector_reversal (chart_neg ht), neg_neg]

#print axioms scaledBand_schwarz
#print axioms normalizedFiberVector_reversal
#print axioms normalizedFiberVector_imaginary

end Maxwell.Continuum.CellBandFourier
