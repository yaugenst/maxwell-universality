import Maxwell.Continuum.WellKernelPointwise
import Maxwell.Continuum.WellMass

/-! The literal well supplies a nonzero trial vector and an explicit
Rayleigh lower bound for its actual compact Birman--Schwinger operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory

theorem complex_inner_re_ofReal (a b : ℝ) :
    RCLike.re (inner ℂ (a : ℂ) (b : ℂ)) = a * b := by
  rw [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul]
  change b * a = a * b
  ring

def rootVector : ScalarL2 := qw_complex_memLp.toLp _

theorem rootVector_ae : rootVector =ᵐ[volume] fun x => (qw x : ℂ) := MemLp.coeFn_toLp _

theorem rootVector_inner : inner ℂ rootVector rootVector = ((∫ x, w x : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [rootVector_ae] with x hx
  rw [hx, inner_self_eq_norm_sq_to_K]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [← RCLike.ofReal_pow, sq_abs, qw_sq]
  rfl

theorem rootVector_norm_sq : ‖rootVector‖ ^ 2 = ∫ x, w x := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), rootVector_inner]
  rfl

theorem rootVector_ne_zero : rootVector ≠ 0 := by
  intro h
  have hn := rootVector_norm_sq
  rw [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hn
  linarith [w_integral_pos]

def kernelFloor : ℝ := FreeFiber.backgroundAmplitude / (2 : ℝ) ^ 24

theorem kernelFloor_pos : 0 < kernelFloor := by
  have h := FreeFiber.backgroundAmplitude_pos
  unfold kernelFloor
  positivity

def rootAction (x : Space) : ℝ := ∫ y : Space, wellKernel x y * qw y

theorem rootAction_integrable (x : Space) :
    Integrable (fun y : Space => wellKernel x y * qw y) := by
  apply ((wellKernel_integrand rootVector x).re).congr
  filter_upwards [rootVector_ae] with y hy
  rw [hy]
  simp

theorem physicalBirmanSchwinger_root_ae :
    physicalBirmanSchwinger rootVector =ᵐ[volume] fun x => (rootAction x : ℂ) := by
  filter_upwards [physicalBirmanSchwinger_kernel_ae rootVector] with x hx
  rw [hx, rootAction, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [rootVector_ae] with y hy
  rw [hy, Complex.ofReal_mul]

theorem rootAction_lower (x : Space) : kernelFloor * (∫ y, w y) * qw x ≤ rootAction x := by
  by_cases hx : ‖x‖ < 1
  · have hle : (∫ y : Space, (kernelFloor * qw x) * w y) ≤ rootAction x := by
      apply integral_mono_ae (w_integrable.const_mul _) (rootAction_integrable x)
      filter_upwards [volume.ae_ne x] with y hy
      by_cases hyball : ‖y‖ < 1
      · have hk := wellKernel_lower x y hx.le hyball.le (Ne.symm hy)
        have hm := mul_le_mul_of_nonneg_right hk (qw_nonneg y)
        change (kernelFloor * qw x) * w y ≤ wellKernel x y * qw y
        calc
          _ = (kernelFloor * (qw x * qw y)) * qw y := by rw [← qw_sq y]; ring
          _ ≤ _ := hm
      · have hqy : qw y = 0 := (qw_zero_iff y).mpr (le_of_not_gt hyball)
        have hwy : w y = 0 := (w_zero_iff y).mpr (le_of_not_gt hyball)
        simp [hwy, hqy]
    rw [integral_const_mul] at hle
    convert hle using 1
    ring
  · have hq : qw x = 0 := (qw_zero_iff x).mpr (le_of_not_gt hx)
    simp [rootAction, wellKernel, hq]

theorem rootAction_pair_integrable : Integrable (fun x => qw x * rootAction x) := by
  apply ((L2.integrable_inner (𝕜 := ℂ) rootVector (physicalBirmanSchwinger rootVector)).re).congr
  filter_upwards [rootVector_ae, physicalBirmanSchwinger_root_ae] with x hx ht
  rw [hx, ht]
  exact complex_inner_re_ofReal _ _

theorem rootVector_energy :
    (inner ℂ rootVector (physicalBirmanSchwinger rootVector)).re =
      ∫ x, qw x * rootAction x := by
  change RCLike.re (inner ℂ rootVector (physicalBirmanSchwinger rootVector)) = _
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) _ _)]
  apply integral_congr_ae
  filter_upwards [rootVector_ae, physicalBirmanSchwinger_root_ae] with x hx ht
  rw [hx, ht]
  exact complex_inner_re_ofReal _ _

theorem rootVector_energy_lower :
    kernelFloor * (∫ x, w x) ^ 2 ≤
      (inner ℂ rootVector (physicalBirmanSchwinger rootVector)).re := by
  rw [rootVector_energy]
  have h : (∫ x, (kernelFloor * (∫ y, w y)) * w x) ≤
      ∫ x, qw x * rootAction x := by
    apply integral_mono_ae (w_integrable.const_mul _) rootAction_pair_integrable
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      have hm := mul_le_mul_of_nonneg_left (rootAction_lower x) (qw_nonneg x)
      calc
        _ = qw x * (kernelFloor * (∫ y, w y) * qw x) := by rw [← qw_sq x]; ring
        _ ≤ _ := hm)
  rw [integral_const_mul] at h
  convert h using 1
  ring

theorem physicalBirmanSchwinger_norm_lower_mass :
    kernelFloor * (∫ x, w x) ≤ ‖physicalBirmanSchwinger‖ := by
  have hu : (inner ℂ rootVector (physicalBirmanSchwinger rootVector)).re ≤
      ‖physicalBirmanSchwinger‖ * ‖rootVector‖ ^ 2 := by
    change RCLike.re (inner ℂ rootVector (physicalBirmanSchwinger rootVector)) ≤ _
    calc
      _ ≤ ‖rootVector‖ * ‖physicalBirmanSchwinger rootVector‖ := re_inner_le_norm (𝕜 := ℂ) _ _
      _ ≤ ‖rootVector‖ * (‖physicalBirmanSchwinger‖ * ‖rootVector‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring
  rw [rootVector_norm_sq] at hu
  have h := rootVector_energy_lower.trans hu
  nlinarith [w_integral_pos]

theorem physicalBirmanSchwinger_norm_lower :
    FreeFiber.backgroundAmplitude / (2 : ℝ) ^ 27 ≤ ‖physicalBirmanSchwinger‖ := by
  apply le_trans _ physicalBirmanSchwinger_norm_lower_mass
  have h := mul_le_mul_of_nonneg_left w_integral_lower kernelFloor_pos.le
  convert h using 1
  unfold kernelFloor
  ring

theorem physicalBirmanSchwinger_ne_zero : physicalBirmanSchwinger ≠ 0 := by
  have h := physicalBirmanSchwinger_norm_lower
  have hρ := FreeFiber.backgroundAmplitude_pos
  intro he
  rw [he, norm_zero] at h
  have hp : 0 < FreeFiber.backgroundAmplitude / (2 : ℝ) ^ 27 := by positivity
  linarith

end Maxwell.Continuum.Well
