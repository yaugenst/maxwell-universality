import Maxwell.Continuum.L1Convolution
import Maxwell.Continuum.EffectiveMassFourierInverse
import Maxwell.Continuum.WellMultiplier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! The Bochner L¹ convolution is the literal Fourier conjugate of a
bounded scalar multiplier when its inverse Fourier integral is that
coefficient. The proof first identifies the pointwise convolution on
L¹ ∩ L² and then uses actual Schwartz density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory FourierTransform

variable (k : Space → ℂ) (hk : Integrable k)

include hk

theorem convolution_inner (f φ : ScalarL2) :
    inner ℂ φ (convolution k hk f) = ∫ y : Space, k y * inner ℂ φ (shift y f) := by
  rw [convolution_apply, ← integral_inner (convolution_integrable k hk f)]
  simp only [inner_smul_right]

theorem convolution_ae (f : ScalarL2) (hf : Integrable (fun x => f x)) :
    convolution k hk f =ᵐ[volume] fun x : Space => ∫ y : Space, k y * f (x-y) := by
  have hprod := hk.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf
  have hc := hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne
  · exact fun _ _ _ => hc.integrableOn
  · intro s hs hμs
    rw [← L2.inner_indicatorConstLp_one hs hμs.ne, convolution_inner]
    calc
      _ = ∫ y : Space, ∫ x : Space in s, k y * f (x-y) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          dsimp only
          rw [L2.inner_indicatorConstLp_one, ← integral_const_mul]
          apply setIntegral_congr_ae hs
          filter_upwards [shift_ae y f] with x hx _
          rw [hx]
      _ = _ := by
        apply (integral_integral_swap ?_).symm
        exact hprod.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)

theorem convolution_result_integrable (f : ScalarL2) (hf : Integrable (fun x => f x)) :
    Integrable (fun x => convolution k hk f x) :=
  (hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf).congr
    (convolution_ae k hk f hf).symm

theorem fourierInv_convolution_ae (f : ScalarL2) (hf : Integrable (fun x => f x)) :
    𝓕⁻ (convolution k hk f) =ᵐ[volume] fun x => 𝓕⁻ k x * 𝓕⁻ (fun y => f y) x := by
  filter_upwards [fourierInvL2_ae_integral (convolution k hk f)
    (convolution_result_integrable k hk f hf)] with x hx
  rw [hx, Real.fourierInv_congr_ae (convolution_ae k hk f hf) x]
  simp only [Real.fourierInv_eq_fourier_neg]
  exact Real.fourier_mul_convolution_eq hk hf (-x)

theorem fourierInv_convolution_multiplier_schwartz (b : Well.UnitProfile)
    (hb : ∀ x : Space, 𝓕⁻ k x = (b.coefficient x : ℂ)) (f : SchwartzMap Space ℂ) :
    𝓕⁻ (convolution k hk (f.toLp 2)) = b.multiplier (𝓕⁻ (f.toLp 2)) := by
  have hf : Integrable (fun x => (f.toLp 2 : ScalarL2) x) :=
    f.integrable.congr (f.coeFn_toLp 2).symm
  apply Lp.ext
  filter_upwards [fourierInv_convolution_ae k hk (f.toLp 2) hf,
    fourierInvL2_ae_integral (f.toLp 2) hf, b.multiplier_ae (𝓕⁻ (f.toLp 2))]
    with x hc hf hm
  rw [hc, hm, hf, hb]

theorem fourierInv_convolution_multiplier (b : Well.UnitProfile)
    (hb : ∀ x : Space, 𝓕⁻ k x = (b.coefficient x : ℂ)) (f : ScalarL2) :
    𝓕⁻ (convolution k hk f) = b.multiplier (𝓕⁻ f) := by
  apply DenseRange.induction_on
    (p := fun f : ScalarL2 => 𝓕⁻ (convolution k hk f) = b.multiplier (𝓕⁻ f))
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (continuous_fourierInv.comp (convolution k hk).continuous)
      (b.multiplier.continuous.comp continuous_fourierInv)
  · exact fourierInv_convolution_multiplier_schwartz k hk b hb

theorem convolution_fourier_multiplier (b : Well.UnitProfile)
    (hb : ∀ x : Space, 𝓕⁻ k x = (b.coefficient x : ℂ)) (f : ScalarL2) :
    convolution k hk (𝓕 f) = 𝓕 (b.multiplier f) := by
  have he := fourierInv_convolution_multiplier k hk b hb (𝓕 f)
  rw [fourierInv_fourier_eq] at he
  simpa only [fourier_fourierInv_eq] using congrArg (fun u : ScalarL2 => 𝓕 u) he

#print axioms convolution_ae
#print axioms convolution_fourier_multiplier

end Maxwell.Continuum.KernelIntegral
