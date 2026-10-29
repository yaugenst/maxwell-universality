import Maxwell.Continuum.WellPhysicalBounds
import Maxwell.Continuum.KernelConvolutionFourier

/-! The literal auxiliary well Birman--Schwinger operator is compact.
Its Green-kernel realization is derived from the exact Fourier identity,
not supplied as spectral data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Well

open MeasureTheory FourierTransform

theorem qw_memLp : MemLp qw 2 (volume : Measure Space) := by
  apply (memLp_two_iff_integrable_sq qw_contDiff.continuous.aestronglyMeasurable).mpr
  simpa only [qw_sq] using w_integrable

theorem qw_complex_memLp : MemLp (fun x => (qw x : ℂ)) 2 (volume : Measure Space) :=
  qw_memLp.ofReal

theorem physicalKernelL2_integrable : Integrable (fun x => physicalKernelL2 x) :=
  physicalKernel_integrable.ofReal.congr physicalKernelL2_ae.symm

def physicalKernelOperator : ScalarL2 →L[ℂ] ScalarL2 :=
  KernelIntegral.weightedConvolution (fun x => (qw x : ℂ)) qw_complex_memLp physicalKernelL2

theorem physicalKernelOperator_compact : IsCompactOperator physicalKernelOperator :=
  KernelIntegral.weightedConvolution_compact _ _ _

theorem rootMultiplier_ae (f : ScalarL2) :
    rootProfile.multiplier f =ᵐ[volume] fun x => f x * (qw x : ℂ) := by
  filter_upwards [rootProfile.multiplier_ae f] with x hx
  exact hx.trans (mul_comm _ _)

theorem rootMultiplier_integrable (f : ScalarL2) :
    Integrable (fun x => rootProfile.multiplier f x) :=
  (KernelIntegral.weighted_source_integrable _ qw_complex_memLp f).congr
    (rootMultiplier_ae f).symm

theorem physicalKernelL2_fourier (ξ : Space) :
    𝓕 (fun x => physicalKernelL2 x) ξ =
      ((1 + ellipticSymbol PeriodicBand.hessianOperator ξ)⁻¹ : ℝ) := by
  rw [Real.fourier_congr_ae physicalKernelL2_ae ξ]
  exact physicalKernel_fourier ξ

theorem physicalKernelOperator_eq :
    physicalKernelOperator = physicalResolvent.comp rootProfile.multiplier := by
  apply ContinuousLinearMap.ext
  intro f
  apply scalarFourier.injective
  apply Lp.ext
  have hkernel := KernelIntegral.weightedConvolution_fourier_ae
    (fun x => (qw x : ℂ)) qw_complex_memLp physicalKernelL2 physicalKernelL2_integrable f
  have hsource := fourierL2_ae_integral (rootProfile.multiplier f) (rootMultiplier_integrable f)
  have hres := resolvent_fourier_ae PeriodicBand.hessianOperator
    PeriodicBand.hessianOperator_nonneg (rootProfile.multiplier f)
  filter_upwards [hkernel, hsource, hres] with ξ hk hs hr
  change (𝓕 (physicalKernelOperator f) : ScalarL2) ξ =
    scalarFourier (physicalResolvent (rootProfile.multiplier f)) ξ
  unfold physicalKernelOperator physicalResolvent
  rw [hk, hr, physicalKernelL2_fourier]
  change _ = _ * (𝓕 (rootProfile.multiplier f) : ScalarL2) ξ
  rw [hs, Real.fourier_congr_ae (rootMultiplier_ae f) ξ]
  ring

theorem physicalResolvent_root_compact :
    IsCompactOperator (physicalResolvent.comp rootProfile.multiplier) := by
  rw [← physicalKernelOperator_eq]
  exact physicalKernelOperator_compact

theorem physicalBirmanSchwinger_compact : IsCompactOperator physicalBirmanSchwinger := by
  exact physicalResolvent_root_compact.clm_comp rootProfile.multiplier

end Maxwell.Continuum.Well
