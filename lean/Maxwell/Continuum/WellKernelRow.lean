import Maxwell.Continuum.WellPerron
import Maxwell.Continuum.MaterialForm

/-! Uniform local L² bounds for the actual Green kernel rows. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory Set Metric

def kernelRow (x : Space) : ScalarL2 :=
  rootProfile.multiplier
    ((physicalKernel_complex_memLp.comp_measurePreserving (measurePreserving_reflect x)).toLp _)

theorem kernelRow_ae (x : Space) :
    kernelRow x =ᵐ[volume] fun y => (qw y * physicalKernel (x - y) : ℝ) := by
  filter_upwards [rootProfile.multiplier_ae
    ((physicalKernel_complex_memLp.comp_measurePreserving (measurePreserving_reflect x)).toLp _),
    (physicalKernel_complex_memLp.comp_measurePreserving (measurePreserving_reflect x)).coeFn_toLp]
      with y hy hz
  change (rootProfile.multiplier _ : ScalarL2) y = _
  rw [hy, hz]
  simp only [rootProfile, Function.comp_apply, Complex.ofReal_mul]

theorem kernelRow_norm_sq (x : Space) :
    ‖kernelRow x‖ ^ 2 = ∫ y : Space, (qw y * physicalKernel (x - y)) ^ 2 := by
  rw [ScalarDielectric.scalar_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [kernelRow_ae x] with y hy
  rw [hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem kernelRow_norm_sq_le (x : Space) (hx : ‖x‖ ≤ 1) :
    ‖kernelRow x‖ ^ 2 ≤ 512 * FreeFiber.backgroundAmplitude ^ 2 := by
  let g : Space → ℝ := (ball 0 2).indicator (fun z => physicalKernel z ^ 2)
  have hg : Integrable g := physicalKernel_sq_integrable.indicator measurableSet_ball
  have hgm : Integrable (fun y => g (x - y)) :=
    hg.comp_sub_left x
  have hr : Integrable (fun y => (qw y * physicalKernel (x - y)) ^ 2) := by
    have h := (Lp.memLp (kernelRow x)).norm
    have hi := (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h
    apply hi.congr
    filter_upwards [kernelRow_ae x] with y hy
    rw [hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hle : (∫ y, (qw y * physicalKernel (x - y)) ^ 2) ≤
      ∫ y, g (x - y) := by
    apply integral_mono hr hgm
    intro y
    dsimp only
    by_cases hy : ‖y‖ < 1
    · have hxy : x - y ∈ ball (0 : Space) 2 := by
        simp only [mem_ball, dist_zero_right]
        exact (norm_sub_le x y).trans_lt (by linarith)
      simp only [g, indicator_of_mem hxy, mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [qw_nonneg y, qw_le_one y])
    · have hq : qw y = 0 := (qw_zero_iff y).mpr (le_of_not_gt hy)
      rw [hq, zero_mul, zero_pow (by norm_num : 2 ≠ 0)]
      exact indicator_nonneg (fun z _ => sq_nonneg (physicalKernel z)) _
  rw [integral_sub_left_eq_self g volume x, integral_indicator measurableSet_ball] at hle
  rw [kernelRow_norm_sq]
  apply hle.trans ((physicalKernel_square_local 2 (by norm_num)).trans _)
  have hp : Real.pi ≤ 4 := Real.pi_lt_four.le
  nlinarith [sq_nonneg FreeFiber.backgroundAmplitude]

def kernelRowBound : ℝ := 32 * FreeFiber.backgroundAmplitude

theorem kernelRowBound_pos : 0 < kernelRowBound := by
  have h := FreeFiber.backgroundAmplitude_pos
  unfold kernelRowBound
  positivity

theorem kernelRow_norm_le (x : Space) (hx : ‖x‖ ≤ 1) :
    ‖kernelRow x‖ ≤ kernelRowBound := by
  have h := kernelRow_norm_sq_le x hx
  have hp := FreeFiber.backgroundAmplitude_pos
  unfold kernelRowBound
  nlinarith [norm_nonneg (kernelRow x)]

theorem absoluteAction_inner (f : ScalarL2) (x : Space) :
    absoluteAction f x = qw x * RCLike.re (inner ℂ (kernelRow x) (absolute f)) := by
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [kernelRow_ae x, absolute_ae f] with y hy hf
  rw [hy, hf, complex_inner_re_ofReal]
  dsimp only [wellKernel]
  ring

theorem absoluteAction_upper (f : ScalarL2) (x : Space) :
    absoluteAction f x ≤ qw x * kernelRowBound * ‖f‖ := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [absoluteAction_inner]
    calc
      _ ≤ qw x * (‖kernelRow x‖ * ‖absolute f‖) :=
        mul_le_mul_of_nonneg_left (re_inner_le_norm (𝕜 := ℂ) _ _) (qw_nonneg x)
      _ ≤ qw x * (kernelRowBound * ‖f‖) := by
        rw [absolute_norm]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (kernelRow_norm_le x hx) (norm_nonneg _)) (qw_nonneg x)
      _ = _ := by ring
  · have hq : qw x = 0 := (qw_zero_iff x).mpr (le_of_not_ge hx)
    simp [absoluteAction, wellKernel, hq]

theorem physicalBirmanSchwinger_norm_pointwise (f : ScalarL2) :
    ∀ᵐ x, ‖physicalBirmanSchwinger f x‖ ≤ qw x * kernelRowBound * ‖f‖ := by
  filter_upwards [physicalBirmanSchwinger_norm_ae_le_absoluteAction f] with x hx
  exact hx.trans (absoluteAction_upper f x)

end Maxwell.Continuum.Well
