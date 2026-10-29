import Maxwell.Continuum.WellIntegralOperator

/-! The positive, symmetric scalar kernel of the literal well operator,
including pointwise integral existence and its almost-everywhere action. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory

theorem measurePreserving_reflect (x : Space) :
    MeasurePreserving (fun y : Space => x - y) volume volume := by
  exact Measure.measurePreserving_sub_left volume x

def wellKernel (x y : Space) : ℝ := qw x * physicalKernel (x - y) * qw y

theorem wellKernel_nonneg (x y : Space) : 0 ≤ wellKernel x y :=
  mul_nonneg (mul_nonneg (qw_nonneg x) (physicalKernel_nonneg _)) (qw_nonneg y)

theorem physicalKernel_neg (x : Space) : physicalKernel (-x) = physicalKernel x :=
  resolventKernel_neg _ _

theorem wellKernel_symm (x y : Space) : wellKernel x y = wellKernel y x := by
  have h : physicalKernel (y - x) = physicalKernel (x - y) := by
    rw [← neg_sub x y, physicalKernel_neg]
  simp only [wellKernel, h]
  ring

theorem wellKernel_lower (x y : Space) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hne : x ≠ y) :
    (FreeFiber.backgroundAmplitude / (2 : ℝ) ^ 24) * (qw x * qw y) ≤ wellKernel x y := by
  have hd : ‖x - y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
  have h := physicalKernel_lower (x - y) (sub_ne_zero.mpr hne) hd
  calc
    _ = qw x * (FreeFiber.backgroundAmplitude / (2 : ℝ) ^ 24) * qw y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h (qw_nonneg x)) (qw_nonneg y)

theorem physicalKernelOperator_integrand (f : ScalarL2) (x : Space) :
    Integrable (fun y : Space => (f y * (qw y : ℂ)) * (physicalKernel (x - y) : ℂ)) := by
  have hk := physicalKernel_complex_memLp.comp_measurePreserving
    (measurePreserving_reflect x)
  have hi := (Lp.memLp (rootProfile.multiplier f)).integrable_mul hk
  apply hi.congr
  filter_upwards [rootMultiplier_ae f] with y hy
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [hy]

theorem wellKernel_integrand (f : ScalarL2) (x : Space) :
    Integrable (fun y : Space => (wellKernel x y : ℂ) * f y) := by
  have h := (physicalKernelOperator_integrand f x).const_mul (qw x : ℂ)
  convert h using 1
  funext y
  simp only [wellKernel, Complex.ofReal_mul]
  ring

theorem physicalKernelOperator_ae (f : ScalarL2) :
    physicalKernelOperator f =ᵐ[volume] fun x =>
      ∫ y : Space, (f y * (qw y : ℂ)) * (physicalKernel (x - y) : ℂ) := by
  have h := KernelIntegral.weightedConvolution_ae (fun x => (qw x : ℂ))
    qw_complex_memLp physicalKernelL2 physicalKernelL2_integrable f
  filter_upwards [h] with x hx
  refine hx.trans ?_
  apply integral_congr_ae
  have he := (measurePreserving_reflect x).quasiMeasurePreserving.ae_eq_comp
    physicalKernelL2_ae
  filter_upwards [he] with y hy
  dsimp only [Function.comp_apply] at hy
  rw [hy]

theorem physicalBirmanSchwinger_kernel_ae (f : ScalarL2) :
    physicalBirmanSchwinger f =ᵐ[volume]
      fun x => ∫ y : Space, (wellKernel x y : ℂ) * f y := by
  have he : physicalBirmanSchwinger f = rootProfile.multiplier (physicalKernelOperator f) := by
    rw [physicalKernelOperator_eq]
    rfl
  rw [he]
  filter_upwards [rootProfile.multiplier_ae (physicalKernelOperator f),
    physicalKernelOperator_ae f] with x hx hi
  rw [hx, hi, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    simp only [rootProfile, wellKernel, Complex.ofReal_mul]
    ring)

end Maxwell.Continuum.Well
