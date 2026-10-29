import Maxwell.Continuum.PeriodicBandComparison
import Maxwell.Continuum.PeriodicVelocity
import Maxwell.Continuum.FiberEnergy
import Maxwell.Continuum.EvenTaylor
import Maxwell.Continuum.CornerBridgeQuadratic
import Maxwell.Continuum.RankOneBandAffine

/-! Holomorphic line slices of the actual Maxwell band and the affine
corner comparison. The affine Hessian is derived from the constructed root. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge Metric Set Filter
open scoped Topology

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot
  scaledBand cornerBand

theorem scaledBand_real (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    (scaledBand (realMomentum t)).im = 0 :=
  actual_kernel_scaledEnergy_im_zero t _ (actual_band_eigenvector ht)

def scaledSlice (t : Momentum) (z : ℂ) : ℂ := scaledBand (z • t)

def cornerSlice (t : Momentum) (z : ℂ) : ℂ := cornerBand (z • t)

theorem line_analytic (t : Momentum) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => w • t) z := analyticAt_id.smul analyticAt_const

theorem line_chart_eventually (t : Momentum) : ∀ᶠ z : ℂ in 𝓝 0, z • t ∈ chart := by
  have hopen : IsOpen {z : ℂ | z • t ∈ chart} :=
    chart_isOpen.preimage (continuous_id.smul continuous_const)
  exact hopen.mem_nhds (by change (0 : ℂ) • t ∈ chart; rw [zero_smul]; exact chart_zero)

theorem scaledSlice_analyticAt_zero (t : Momentum) : AnalyticAt ℂ (scaledSlice t) 0 := by
  have hf : AnalyticAt ℂ scaledBand ((0 : ℂ) • t) := by
    simpa only [zero_smul] using scaledBand_analytic 0 chart_zero
  exact AnalyticAt.comp (f := fun w : ℂ => w • t) hf (line_analytic t 0)

theorem cornerSlice_analyticAt_zero (t : Momentum) : AnalyticAt ℂ (cornerSlice t) 0 := by
  have hf : AnalyticAt ℂ cornerBand ((0 : ℂ) • t) := by
    simpa only [zero_smul] using cornerBand_analytic 0 chart_zero
  exact AnalyticAt.comp (f := fun w : ℂ => w • t) hf (line_analytic t 0)

theorem scaledSlice_even (t : Momentum) :
    (fun z => scaledSlice t (-z)) =ᶠ[𝓝 0] scaledSlice t := by
  filter_upwards [line_chart_eventually t] with z hz
  simpa only [scaledSlice, neg_smul] using scaledBand_neg hz

theorem scaledSlice_first_zero (t : Momentum) : deriv (scaledSlice t) 0 = 0 := by
  simpa only [Nat.mul_zero, zero_add, iteratedDeriv_one] using
    EvenTaylor.odd_deriv_zero (scaledSlice_even t) 0

theorem line_mem_chart {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1) {z : ℂ}
    (hz : ‖z‖ < ((2 : ℝ) ^ 12)⁻¹) : z • t ∈ chart := by
  intro j
  change ‖z * t j‖ < _
  rw [norm_mul]
  exact ((mul_le_mul_of_nonneg_left (ht j) (norm_nonneg z)).trans_eq
    (mul_one _)).trans_lt hz

theorem scaledSlice_analytic {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1) :
    AnalyticOnNhd ℂ (scaledSlice t) (ball 0 (((2 : ℝ) ^ 12)⁻¹)) := by
  intro z hz
  have hz' : ‖z‖ < ((2 : ℝ) ^ 12)⁻¹ := by
    simpa only [mem_ball, dist_zero_right] using hz
  exact AnalyticAt.comp (f := fun w : ℂ => w • t)
    (scaledBand_analytic _ (line_mem_chart ht hz')) (line_analytic t z)

theorem cornerSlice_analytic {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1) :
    AnalyticOnNhd ℂ (cornerSlice t) (ball 0 (((2 : ℝ) ^ 12)⁻¹)) := by
  intro z hz
  have hz' : ‖z‖ < ((2 : ℝ) ^ 12)⁻¹ := by
    simpa only [mem_ball, dist_zero_right] using hz
  exact AnalyticAt.comp (f := fun w : ℂ => w • t)
    (cornerBand_analytic _ (line_mem_chart ht hz')) (line_analytic t z)

theorem cornerSlice_derivatives (t : Corner.Vec) :
    deriv (cornerSlice (realMomentum t)) 0 = 0 ∧
    deriv (deriv (cornerSlice (realMomentum t))) 0 = 2 * (cornerQuadratic t : ℂ) := by
  have h0 : cornerSlice (realMomentum t) 0 = (Corner.lambdaStar : ℂ) := by
    rw [cornerSlice, zero_smul, cornerBand_zero]
  have hroot : ∀ᶠ z : ℂ in 𝓝 0,
      RankOneBand.rootMap finiteK topState Corner.lambdaStar
        (z • finiteVelocity (realMomentum t)) (cornerSlice (realMomentum t) z) =
          cornerSlice (realMomentum t) z := by
    filter_upwards [line_chart_eventually (realMomentum t)] with z hz
    have h := actualCornerData.bandRoot_fixed cornerPerturbationData (z • realMomentum t) hz
    rw [show actualCornerData.bandRoot cornerPerturbationData (z • realMomentum t) =
      cornerSlice (realMomentum t) z by unfold cornerSlice cornerBand; rfl] at h
    rwa [finiteVelocity_smul] at h
  have h := actualCornerData.affine_branch_derivatives (finiteVelocity (realMomentum t))
    (cornerSlice_analyticAt_zero _) h0 hroot
  change deriv (cornerSlice (realMomentum t)) 0 =
    inner ℂ topState (finiteVelocity (realMomentum t) topState) ∧
    deriv (deriv (cornerSlice (realMomentum t))) 0 =
      2 * inner ℂ topState (finiteVelocity (realMomentum t)
        (RankOneBand.embed topState (actualCornerData.baseInverse
          (RankOneBand.project topState (finiteVelocity (realMomentum t) topState))))) at h
  rwa [topState_velocity_mean, affineCoefficient_identity] at h

end Maxwell.Continuum.PeriodicBand
