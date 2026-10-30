import Maxwell.Continuum.FiniteWellMaterial
import Maxwell.Continuum.WellFourierTail
import Maxwell.Continuum.L1ConvolutionFourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Literal Fourier kernels of the translated, dilated physical well.
The Jacobian and phase factors are proved from the Fourier integrals. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Auxiliary

open MeasureTheory FourierTransform Bloch

private theorem fourier_dilate (f : Space → ℂ) {h : ℝ} (hh : 0 < h) (ξ : Space) :
    𝓕 (fun x => f (h • x)) ξ = (h^3)⁻¹ • 𝓕 f (h⁻¹ • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have he (x : Space) : inner ℝ (h • x) (h⁻¹ • ξ) = inner ℝ x ξ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hs := Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    (fun x : Space => (Real.fourierChar (-inner ℝ x (h⁻¹ • ξ)) : ℂ) • f x) h (hR := hh.le)
  simpa only [Space, finrank_euclideanSpace, Fintype.card_fin, he, Circle.smul_def] using hs

def translatedWellKernel (h : ℝ) (r : Space) : Space → ℂ :=
  𝓕 (fun x : Space => (Well.w (h • (x-r)) : ℂ))

theorem translatedWellKernel_formula {h : ℝ} (hh : 0 < h) (r ξ : Space) :
    translatedWellKernel h r ξ =
      (h^3)⁻¹ • (phase (-r) ξ * Well.rawPhysicalFourier Well.w ((2*Real.pi/h) • ξ)) := by
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure Space) (innerₗ Space)
    (fun x : Space => (Well.w (h • x) : ℂ)) (-r)) ξ
  have ht' : 𝓕 (fun x : Space => (Well.w (h • (x + -r)) : ℂ)) ξ =
      phase (-r) ξ * 𝓕 (fun x : Space => (Well.w (h • x) : ℂ)) ξ := by
    change 𝓕 (fun x : Space => (Well.w (h • (x + -r)) : ℂ)) ξ =
      (Real.fourierChar (inner ℝ (-r) ξ) : ℂ) *
        𝓕 (fun x : Space => (Well.w (h • x) : ℂ)) ξ at ht
    simpa only [Function.comp_apply, phase, Circle.smul_def, smul_eq_mul,
      real_inner_comm (-r) ξ] using ht
  have hd := fourier_dilate (Well.complexify Well.w) hh ξ
  change 𝓕 (fun x : Space => (Well.w (h • x) : ℂ)) ξ =
    (h^3)⁻¹ • 𝓕 (Well.complexify Well.w) (h⁻¹ • ξ) at hd
  rw [hd] at ht'
  have he : (2*Real.pi)⁻¹ • ((2*Real.pi/h) • ξ) = h⁻¹ • ξ := by
    rw [smul_smul]
    congr 1
    field_simp
  change 𝓕 (fun x : Space => (Well.w (h • (x-r)) : ℂ)) ξ = _
  rw [show (fun x : Space => (Well.w (h • (x-r)) : ℂ)) =
    (fun x : Space => (Well.w (h • (x + -r)) : ℂ)) from rfl, ht']
  simp only [Well.rawPhysicalFourier, he]
  exact mul_smul_comm _ _ _

theorem translatedWellKernel_norm {h : ℝ} (hh : 0 < h) (r ξ : Space) :
    ‖translatedWellKernel h r ξ‖ = (h^3)⁻¹ *
      ‖Well.rawPhysicalFourier Well.w ((2*Real.pi/h) • ξ)‖ := by
  rw [translatedWellKernel_formula hh, norm_smul, norm_mul, phase_norm, one_mul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (h^3)⁻¹)]

theorem rawWellFourier_continuous : Continuous (Well.rawPhysicalFourier Well.w) := by
  have hw : Integrable (Well.complexify Well.w) :=
    Complex.ofRealCLM.integrable_comp Well.w_integrable
  have hF : Continuous (𝓕 (Well.complexify Well.w)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by change Continuous (fun p : Space × Space => inner ℝ p.1 p.2); fun_prop) hw
  exact hF.comp (by fun_prop : Continuous (fun p : Space => (2*Real.pi)⁻¹ • p))

theorem rawWellFourier_decay (p : Space) :
    ‖Well.rawPhysicalFourier Well.w p‖ ≤ (2 : ℝ)^20 * Real.exp (-Real.sqrt ‖p‖/256) := by
  have hb := Well.rawPhysicalFourier_decay Well.w Well.w_contDiff Well.w_hasCompactSupport
    (by rw [Well.w_tsupport]) (fun K y v hv => Well.w_directional_gevrey y v hv K) p
  apply hb.trans
  apply mul_le_mul (by norm_num : (24 : ℝ) ≤ 2^20) _ (Real.exp_pos _).le (by positivity)
  exact Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg ‖p‖])

theorem rawWellFourier_integrable : Integrable (Well.rawPhysicalFourier Well.w) := by
  apply (Well.tailMajorant_integrable.const_mul ((2 : ℝ)^20)).mono'
    rawWellFourier_continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => (rawWellFourier_decay p).trans (by
    change (2 : ℝ)^20 * Real.exp (-Real.sqrt ‖p‖/256) ≤
      (2 : ℝ)^20 * Real.exp (-Real.sqrt ‖p‖/512)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg ‖p‖]))

theorem translatedWellKernel_integrable {h : ℝ} (hh : 0 < h) (r : Space) :
    Integrable (translatedWellKernel h r) := by
  have hc : Continuous (translatedWellKernel h r) := by
    have he : translatedWellKernel h r = fun ξ => (h^3)⁻¹ •
        (phase (-r) ξ * Well.rawPhysicalFourier Well.w ((2*Real.pi/h) • ξ)) :=
      funext (translatedWellKernel_formula hh r)
    rw [he]
    exact (continuous_const : Continuous (fun _ : Space => (h^3)⁻¹)).smul ((phase_continuous _).mul
      (rawWellFourier_continuous.comp
        (by fun_prop : Continuous (fun ξ : Space => (2*Real.pi/h) • ξ))))
  apply ((rawWellFourier_integrable.comp_smul
    (by positivity : 2*Real.pi/h ≠ 0)).norm.const_mul ((h^3)⁻¹)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => (translatedWellKernel_norm hh r ξ).le

theorem translatedWellKernel_inverse {h : ℝ} (hh : 0 < h) (r x : Space) :
    𝓕⁻ (translatedWellKernel h r) x = (Well.w (h • (x-r)) : ℂ) := by
  have hw : Integrable (fun x : Space => (Well.w (h • (x-r)) : ℂ)) := by
    simpa only [sub_eq_add_neg, Complex.ofRealCLM_apply] using
      ((Complex.ofRealCLM.integrable_comp Well.w_integrable).comp_smul hh.ne').comp_add_right (-r)
  exact hw.fourierInv_fourier_eq (translatedWellKernel_integrable hh r)
    ((Complex.continuous_ofReal.comp (Well.w_contDiff.continuous.comp
      ((continuous_id.sub continuous_const).const_smul h))).continuousAt)

theorem translatedWell_fourier_convolution {h : ℝ} (hh : 0 < h) (r : Space) (f : ScalarL2) :
    KernelIntegral.convolution (translatedWellKernel h r) (translatedWellKernel_integrable hh r)
      (𝓕 f) = 𝓕 ((translatedWellProfile h r).multiplier f) :=
  KernelIntegral.convolution_fourier_multiplier _ _ (translatedWellProfile h r)
    (translatedWellKernel_inverse hh r) f

#print axioms translatedWellKernel_formula
#print axioms translatedWell_fourier_convolution

end Maxwell.Continuum.Auxiliary
