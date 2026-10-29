import Maxwell.Continuum.WellPhysical
import Maxwell.Continuum.WellKernelMinorization
import Maxwell.Continuum.WellCoulombSquare

/-! The actual physical Green kernel has the explicit near-diagonal
minorization and Coulomb upper bound, and belongs to L¹ and L². -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set Metric

theorem physicalKernel_nonneg (x : Space) : 0 ≤ physicalKernel x :=
  resolventKernel_nonneg _ _

theorem physicalKernel_integral : (∫ x, physicalKernel x) = 1 :=
  resolventKernel_integral _ physicalCoefficients_ne_zero

theorem physicalKernel_upper (x : Space) (hx : x ≠ 0) :
    physicalKernel x ≤ 4 * FreeFiber.backgroundAmplitude / ‖x‖ := by
  apply resolventKernel_quantitative_upper physicalCoefficients physicalCoefficients_ne_zero
    FreeFiber.backgroundAmplitude FreeFiber.backgroundAmplitude_pos _ _ x hx
  · exact fun i => (physical_diagonal_bounds i).1
  · exact fun i => (physical_diagonal_bounds i).2

theorem physicalKernel_lower (x : Space) (hx : x ≠ 0) (hxu : ‖x‖ ≤ 2) :
    FreeFiber.backgroundAmplitude / (2 : ℝ) ^ 24 ≤ physicalKernel x := by
  apply resolventKernel_quantitative_lower physicalCoefficients physicalCoefficients_ne_zero
    FreeFiber.backgroundAmplitude FreeFiber.backgroundAmplitude_pos _ _ _ x hx hxu
  · norm_num [FreeFiber.backgroundAmplitude]
  · exact fun i => (physical_diagonal_bounds i).1
  · exact fun i => (physical_diagonal_bounds i).2

theorem physicalKernel_sq_upper (x : Space) (hx : x ≠ 0) :
    physicalKernel x ^ 2 ≤
      16 * FreeFiber.backgroundAmplitude ^ 2 * (‖x‖ ^ 2)⁻¹ := by
  have h := physicalKernel_upper x hx
  have hp := physicalKernel_nonneg x
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : (4 * FreeFiber.backgroundAmplitude / ‖x‖) ^ 2 =
      16 * FreeFiber.backgroundAmplitude ^ 2 * (‖x‖ ^ 2)⁻¹ := by ring
  rw [← he]
  exact pow_le_pow_left₀ hp h 2

theorem physicalKernel_sq_integrable : Integrable (fun x => physicalKernel x ^ 2) := by
  let ρ := FreeFiber.backgroundAmplitude
  have hρ : 0 < ρ := FreeFiber.backgroundAmplitude_pos
  have hi₀ : Integrable ((ball (0 : Space) 1).indicator (fun x => (‖x‖ ^ 2)⁻¹)) :=
    (integrable_indicator_iff measurableSet_ball).mpr (inverseSquare_integrable_ball 1)
  have hi := hi₀.const_mul (16 * ρ ^ 2)
  have hj := physicalKernel_integrable.const_mul (4 * ρ)
  apply (hi.add hj).mono' (physicalKernel_integrable.aestronglyMeasurable.pow 2)
  have hn : ∀ᵐ x : Space, x ≠ 0 := volume.ae_ne 0
  filter_upwards [hn] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases h : ‖x‖ < 1
  · have hxball : x ∈ ball (0 : Space) 1 := by simpa using h
    simp only [Pi.add_apply, indicator_of_mem hxball]
    exact (physicalKernel_sq_upper x hx).trans
      (le_add_of_nonneg_right (mul_nonneg (by positivity) (physicalKernel_nonneg x)))
  · have hxball : x ∉ ball (0 : Space) 1 := by simpa using h
    simp only [Pi.add_apply, indicator_of_notMem hxball, mul_zero, zero_add]
    have hle : physicalKernel x ≤ 4 * ρ := by
      apply (physicalKernel_upper x hx).trans
      exact div_le_self (by positivity) (le_of_not_gt h)
    change physicalKernel x ^ 2 ≤ 4 * ρ * physicalKernel x
    nlinarith [physicalKernel_nonneg x]

theorem physicalKernel_memLp : MemLp physicalKernel 2 (volume : Measure Space) :=
  (memLp_two_iff_integrable_sq physicalKernel_integrable.aestronglyMeasurable).mpr
    physicalKernel_sq_integrable

theorem physicalKernel_complex_memLp :
    MemLp (fun x => (physicalKernel x : ℂ)) 2 (volume : Measure Space) :=
  physicalKernel_memLp.ofReal

def physicalKernelL2 : ScalarL2 := physicalKernel_complex_memLp.toLp _

theorem physicalKernelL2_ae :
    physicalKernelL2 =ᵐ[volume] fun x => (physicalKernel x : ℂ) :=
  MemLp.coeFn_toLp _

theorem physicalKernel_square_local (R : ℝ) (hR : 0 ≤ R) :
    (∫ x : Space in ball 0 R, physicalKernel x ^ 2) ≤
      64 * Real.pi * FreeFiber.backgroundAmplitude ^ 2 * R := by
  have hm := (inverseSquare_integrable_ball R).const_mul
    (16 * FreeFiber.backgroundAmplitude ^ 2)
  have hn : ∀ᵐ x : Space ∂volume.restrict (ball 0 R), x ≠ 0 := by
    exact ae_restrict_of_ae (volume.ae_ne 0)
  have hle : (∫ x : Space in ball 0 R, physicalKernel x ^ 2) ≤
      ∫ x : Space in ball 0 R,
        16 * FreeFiber.backgroundAmplitude ^ 2 * (‖x‖ ^ 2)⁻¹ := by
    apply integral_mono_ae physicalKernel_sq_integrable.integrableOn hm
    filter_upwards [hn] with x hx
    exact physicalKernel_sq_upper x hx
  rw [integral_const_mul, inverseSquare_integral_ball R hR] at hle
  convert hle using 1
  ring

end Maxwell.Continuum.Well
