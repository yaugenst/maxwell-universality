import Maxwell.Continuum.FiberNormalizationVector
import Maxwell.Continuum.PeriodicBandSlices

/-! Reality of the actual analytically chosen infinite-fiber eigenvector
at real momentum follows from conjugation of the maximal graph, simplicity
of its kernel, and the fixed coefficient gauge. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiberNormalization

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge PeriodicBand

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot
  scaledBand clusterVector fiberVector

theorem scaledBand_star (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    star (scaledBand (realMomentum t)) = scaledBand (realMomentum t) := by
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
  · simp only [Complex.star_def, Complex.conj_im, scaledBand_real t ht, neg_zero]

theorem totalEnergy_scaledBand_star (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    star (totalEnergy (scaledBand (realMomentum t))) =
      totalEnergy (scaledBand (realMomentum t)) := by
  simp only [totalEnergy, star_add, star_mul', scaledBand_star t ht]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem fiberVector_star_graph (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    (star (fiberVector (realMomentum t)), 0) ∈
      (materialFiber (scaledMomentum (realMomentum t))
        (totalEnergy (scaledBand (realMomentum t))) backgroundAmplitude).graph := by
  have h := material_graph_star _ _ backgroundAmplitude _ _ (fiberVector_graph ht)
  rw [star_zero, totalEnergy_scaledBand_star t ht, scaledMomentum_real,
    star_realMomentum] at h
  simpa only [scaledMomentum_real] using h

theorem fiberVector_star_gauge {t : Momentum} (ht : t ∈ chart) :
    inner ℂ topState.val (star (fiberVector t)) = 1 := by
  have h := fiber_inner_star topState.val (fiberVector t)
  rw [topState_star, fiberVector_gauge ht, star_one] at h
  exact h

theorem fiberVector_real (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    star (fiberVector (realMomentum t)) = fiberVector (realMomentum t) := by
  obtain ⟨x, hx, hx0⟩ := (LinearPMap.mem_graph_iff _).mp (fiberVector_graph ht)
  obtain ⟨y, hy, hy0⟩ := (LinearPMap.mem_graph_iff _).mp (fiberVector_star_graph t ht)
  let xk : ActualKernel (realMomentum t) (scaledBand (realMomentum t)) := ⟨x, hx0⟩
  let yk : ActualKernel (realMomentum t) (scaledBand (realMomentum t)) := ⟨y, hy0⟩
  have hxk : xk ≠ 0 := by
    intro h
    have hv := congrArg (fun z : ActualKernel (realMomentum t) (scaledBand (realMomentum t)) =>
      z.val.val) h
    change x.val = 0 at hv
    rw [hx] at hv
    exact fiberVector_ne_zero ht hv
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one (actual_band_kernel_finrank ht) hxk yk
  have hav := congrArg (fun z : ActualKernel (realMomentum t) (scaledBand (realMomentum t)) =>
    z.val.val) ha
  change a • x.val = y.val at hav
  rw [hx, hy] at hav
  have hcoef := congrArg (fun v : FiberSpace => inner ℂ topState.val v) hav
  rw [inner_smul_right, fiberVector_gauge ht, fiberVector_star_gauge ht, mul_one] at hcoef
  simpa only [hcoef, one_smul] using hav.symm

#print axioms fiberVector_real

end Maxwell.Continuum.FiberNormalization
