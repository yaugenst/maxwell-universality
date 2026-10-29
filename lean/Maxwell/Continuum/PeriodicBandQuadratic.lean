import Maxwell.Continuum.PeriodicBandTaylor
import Maxwell.Continuum.AnalyticLineCoefficients
import Maxwell.Continuum.RealHolomorphicCoefficients

/-! The quadratic coefficient is taken from the actual Fréchet power series
of the Maxwell band. Its homogeneity and reality are proved from that origin. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber CornerBridge Filter
open scoped Topology

def bandSeries : FormalMultilinearSeries ℂ Momentum ℂ :=
  (scaledBand_analytic 0 chart_zero).choose

theorem bandSeries_has : HasFPowerSeriesAt scaledBand bandSeries 0 :=
  (scaledBand_analytic 0 chart_zero).choose_spec

def bandQuadratic (t : Momentum) : ℂ := bandSeries 2 (fun _ => t)

theorem bandQuadratic_eq_coefficient (t : Momentum) :
    bandQuadratic t = EvenTaylor.coefficient (scaledSlice t) 2 :=
  (AnalyticLineCoefficients.coefficient_eq bandSeries_has t 2).symm

theorem bandQuadratic_smul (c : ℂ) (t : Momentum) :
    bandQuadratic (c • t) = c ^ 2 * bandQuadratic t := by
  simp only [bandQuadratic, ContinuousMultilinearMap.map_smul_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem bandQuadratic_zero : bandQuadratic 0 = 0 := by
  simpa only [zero_smul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using
    bandQuadratic_smul 0 (0 : Momentum)

theorem realMomentum_smul (c : ℝ) (t : Corner.Vec) :
    realMomentum (c • t) = (c : ℂ) • realMomentum t := by
  funext j
  simp only [realMomentum, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]

theorem scaledSlice_real_eventually (t : Corner.Vec) :
    ∀ᶠ x : ℝ in 𝓝 0, (scaledSlice (realMomentum t) (x : ℂ)).im = 0 := by
  have hc : Tendsto Complex.ofReal (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hx : ∀ᶠ x : ℝ in 𝓝 0, (x : ℂ) • realMomentum t ∈ chart :=
    hc.eventually (line_chart_eventually (realMomentum t))
  filter_upwards [hx] with x hx
  change (scaledBand ((x : ℂ) • realMomentum t)).im = 0
  rw [← realMomentum_smul] at hx ⊢
  exact scaledBand_real (x • t) hx

theorem bandQuadratic_im_zero (t : Corner.Vec) :
    (bandQuadratic (realMomentum t)).im = 0 := by
  rw [bandQuadratic_eq_coefficient]
  exact RealHolomorphicCoefficients.coefficient_im_zero (scaledSlice_analyticAt_zero _)
    (scaledSlice_real_eventually t) 2

theorem bandQuadratic_ofReal_re (t : Corner.Vec) :
    ((bandQuadratic (realMomentum t)).re : ℂ) = bandQuadratic (realMomentum t) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im, bandQuadratic_im_zero]

theorem cornerQuadratic_smul (c : ℝ) (t : Corner.Vec) :
    cornerQuadratic (c • t) = c ^ 2 * cornerQuadratic t := by
  simp only [cornerQuadratic, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem bandQuadratic_unit_comparison (t : Corner.Vec) (ht : ∀ j, |t j| ≤ 1) :
    ‖bandQuadratic (realMomentum t) - (cornerQuadratic t : ℂ)‖ ≤
      (2 : ℝ) ^ 34 * backgroundAmplitude := by
  rw [bandQuadratic_eq_coefficient]
  exact scaledSlice_quadratic_comparison t ht

end Maxwell.Continuum.PeriodicBand
