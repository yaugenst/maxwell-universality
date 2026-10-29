import Maxwell.Continuum.PeriodicSchurKernel
import Maxwell.Continuum.CornerBridgeGap
import Maxwell.Continuum.RankOneBandFamilyAnalytic

/-! A constructed simple analytic band of the actual infinite periodic
Maxwell fiber. The spectral data and perturbation bounds are proved for the
literal dielectric; no analytic band or eigenvalue-existence premise remains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge Metric Set

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot

theorem perturbationData : RankOneBand.PerturbationData
    (fun t e => perturbation (t, e)) chart Corner.lambdaStar where
  small t ht e he := perturbation_norm_le (t, e) (chart_energy_inBox ht he)
  energy_lipschitz t ht :=
    (perturbation_energy_lipschitz t (chart_closed_bounds ht)).mono energyDisk_subset_four

def scaledBand (t : Momentum) : ℂ := actualCornerData.bandRoot perturbationData t

def clusterVector (t : Momentum) : clusterSpace := actualCornerData.bandVector perturbationData t

theorem scaledBand_mem {t : Momentum} (ht : t ∈ chart) : scaledBand t ∈ energyDisk :=
  actualCornerData.bandRoot_mem perturbationData t ht

theorem scaledBand_center_bound {t : Momentum} (ht : t ∈ chart) :
    ‖scaledBand t - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 200 :=
  actualCornerData.bandRoot_center_bound perturbationData t ht

theorem scaledBand_norm_le {t : Momentum} (ht : t ∈ chart) : ‖scaledBand t‖ ≤ 3 :=
  energy_norm_le (scaledBand_mem ht)

theorem scaledBand_analytic : AnalyticOnNhd ℂ scaledBand chart := by
  unfold scaledBand
  have hfun : Function.uncurry (fun t e => perturbation (t, e)) = perturbation := by
    funext z
    rcases z with ⟨t, e⟩
    rfl
  have hV : AnalyticOnNhd ℂ (Function.uncurry (fun t e => perturbation (t, e)))
      (chart ×ˢ closedBall (Corner.lambdaStar : ℂ) (1 / 100)) := by
    rw [hfun]
    exact chart_energy_analytic
  exact RankOneBand.Data.analyticOnNhd_bandRoot (H := clusterSpace) (E := Momentum)
    (K := finiteK) (u := topState) (ell := Corner.lambdaStar)
    (V := fun t e => perturbation (t, e)) (U := chart)
    actualCornerData perturbationData hV chart_isOpen

theorem clusterVector_analytic : AnalyticOnNhd ℂ clusterVector chart := by
  unfold clusterVector
  have hfun : Function.uncurry (fun t e => perturbation (t, e)) = perturbation := by
    funext z
    rcases z with ⟨t, e⟩
    rfl
  have hV : AnalyticOnNhd ℂ (Function.uncurry (fun t e => perturbation (t, e)))
      (chart ×ˢ closedBall (Corner.lambdaStar : ℂ) (1 / 100)) := by
    rw [hfun]
    exact chart_energy_analytic
  exact RankOneBand.Data.analyticOnNhd_bandVector (H := clusterSpace) (E := Momentum)
    (K := finiteK) (u := topState) (ell := Corner.lambdaStar)
    (V := fun t e => perturbation (t, e)) (U := chart)
    actualCornerData perturbationData hV chart_isOpen

theorem clusterVector_ne_zero (t : Momentum) : clusterVector t ≠ 0 :=
  actualCornerData.bandVector_ne_zero perturbationData t

theorem finiteSchur_eq_bandOperator (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    finiteSchur t e ht he = RankOneBand.operator finiteK (perturbation (t, e)) e :=
  (finiteSchurExtension_eq (t, e) ⟨ht, he⟩).symm.trans
    (finiteSchurExtension_expansion (t, e))

theorem schur_nonzero_iff_scaledBand {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) :
    (∃ x : clusterSpace, x ≠ 0 ∧ finiteSchurExtension (t, e) x = 0) ↔ e = scaledBand t := by
  rw [finiteSchurExtension_expansion]
  exact actualCornerData.kernel_nonzero_iff_bandRoot perturbationData t ht e he

/-- The analytic root is characterized by a nonzero vector in the actual
infinite fiber graph, throughout the specified isolated energy disk. -/
theorem actual_nonzero_iff_scaledBand {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) :
    (∃ u : FiberSpace, u ≠ 0 ∧
      (u, 0) ∈ (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).graph) ↔
      e = scaledBand t :=
  (schurExtension_nonzero_iff_actual t e (chart_closed_bounds ht)
    (chart_energy_inBox ht he).2).symm.trans (schur_nonzero_iff_scaledBand ht he)

theorem actual_band_eigenvector {t : Momentum} (ht : t ∈ chart) :
    ∃ u : FiberSpace, u ≠ 0 ∧
      (u, 0) ∈ (materialFiber (scaledMomentum t)
        (totalEnergy (scaledBand t)) backgroundAmplitude).graph :=
  (actual_nonzero_iff_scaledBand ht (scaledBand_mem ht)).mpr rfl

/-- The actual maximal-domain fiber eigenspace is one-dimensional. -/
theorem actual_band_kernel_finrank {t : Momentum} (ht : t ∈ chart) :
    Module.finrank ℂ (ActualKernel t (scaledBand t)) = 1 := by
  have hb := chart_energy_inBox ht (scaledBand_mem ht)
  have hfinite : Module.finrank ℂ (FiniteKernel t (scaledBand t) hb.1 hb.2) = 1 := by
    change Module.finrank ℂ (LinearMap.ker (finiteSchur t (scaledBand t) hb.1 hb.2).toLinearMap) = 1
    have heq := finiteSchur_eq_bandOperator t (scaledBand t) hb.1 hb.2
    have hker := congrArg (fun A : clusterSpace →L[ℂ] clusterSpace =>
      Module.finrank ℂ A.ker) heq
    have hr := RankOneBand.Data.bandRoot_kernel_finrank (H := clusterSpace) (E := Momentum)
      (K := finiteK) (u := topState) (ell := Corner.lambdaStar)
      (V := fun t e => perturbation (t, e)) (U := chart)
      actualCornerData perturbationData t ht
    rw [show actualCornerData.bandRoot perturbationData t = scaledBand t from rfl] at hr
    exact hker.trans hr
  exact (actualKernel_finrank_eq t (scaledBand t) hb.1 hb.2).trans hfinite

/-- Coordinate evenness follows from the proved polar-vector reflection of
the full infinite fiber and uniqueness of its root in the isolated disk. -/
theorem scaledBand_reflect {t : Momentum} (ht : t ∈ chart) (j : Fin 3) :
    scaledBand (FiberReflection.momentum j t) = scaledBand t := by
  have heig := (FiberReflection.actual_kernel_reflect_iff j t (scaledBand t)).mpr
    (actual_band_eigenvector ht)
  exact ((actual_nonzero_iff_scaledBand (chart_reflect ht j) (scaledBand_mem ht)).mp heig).symm

theorem reflect_all (t : Momentum) :
    FiberReflection.momentum 2 (FiberReflection.momentum 1 (FiberReflection.momentum 0 t)) = -t := by
  funext j
  fin_cases j <;> simp [FiberReflection.momentum, FiberReflection.coordinateSign]

theorem scaledBand_neg {t : Momentum} (ht : t ∈ chart) : scaledBand (-t) = scaledBand t := by
  have h0 := scaledBand_reflect ht 0
  have h1 := scaledBand_reflect (chart_reflect ht 0) 1
  have h2 := scaledBand_reflect (chart_reflect (chart_reflect ht 0) 1) 2
  rw [reflect_all] at h2
  exact h2.trans (h1.trans h0)

end Maxwell.Continuum.PeriodicBand
