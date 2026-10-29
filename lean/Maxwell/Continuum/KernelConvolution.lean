import Maxwell.Continuum.KernelTranslation
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! The compact weighted-convolution construction has the literal
pointwise convolution representative whenever the kernel is also L¹. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory
open scoped ENNReal

theorem weighted_source_integrable (w : Space → ℂ) (hw : MemLp w 2 volume)
    (f : ScalarL2) : Integrable (fun y => f y * w y) :=
  (Lp.memLp f).integrable_mul hw

theorem weightedConvolution_pointwise_integrable (w : Space → ℂ)
    (hw : MemLp w 2 volume) (u : ScalarL2) (hu : Integrable (fun x => u x))
    (f : ScalarL2) :
    Integrable (fun x : Space => ∫ y : Space, (f y * w y) * u (x - y)) := by
  exact (weighted_source_integrable w hw f).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hu

theorem weightedConvolution_ae (w : Space → ℂ) (hw : MemLp w 2 volume)
    (u : ScalarL2) (hu : Integrable (fun x => u x)) (f : ScalarL2) :
    weightedConvolution w hw u f =ᵐ[volume]
      fun x : Space => ∫ y : Space, (f y * w y) * u (x - y) := by
  have hg := weighted_source_integrable w hw f
  have hprod := hg.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hu
  have hc := weightedConvolution_pointwise_integrable w hw u hu f
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne
  · exact fun _ _ _ => hc.integrableOn
  · intro s hs hμs
    rw [← L2.inner_indicatorConstLp_one hs hμs.ne, weightedConvolution_inner]
    calc
      _ = ∫ y : Space, ∫ x : Space in s, (f y * w y) * u (x - y) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y => by
          dsimp only
          rw [L2.inner_indicatorConstLp_one, ← integral_const_mul]
          apply setIntegral_congr_ae hs
          filter_upwards [shift_ae y u] with x hx _
          rw [hx])
      _ = _ := by
        apply (integral_integral_swap ?_).symm
        exact hprod.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)

theorem weightedConvolution_integrable_result (w : Space → ℂ) (hw : MemLp w 2 volume)
    (u : ScalarL2) (hu : Integrable (fun x => u x)) (f : ScalarL2) :
    Integrable (fun x => weightedConvolution w hw u f x) :=
  (weightedConvolution_pointwise_integrable w hw u hu f).congr
    (weightedConvolution_ae w hw u hu f).symm

end Maxwell.Continuum.KernelIntegral
