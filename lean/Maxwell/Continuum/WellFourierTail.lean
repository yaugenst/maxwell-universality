import Maxwell.Continuum.WellFourierDecay
import Maxwell.Continuum.WellRadialTail

/-! The literal well Fourier transforms satisfy the displayed continuum tail bound. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set
open scoped FourierTransform

theorem physicalFourier_eq_integral (f : Space → ℝ) (p : Space) :
    physicalFourier f p = (2 * Real.pi) ^ (-(3 / 2 : ℝ)) •
      ∫ y : Space, Complex.exp (-Complex.I * (inner ℝ p y : ℂ)) * (f y : ℂ) := by
  rw [physicalFourier, rawPhysicalFourier, Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [real_inner_smul_right, real_inner_comm y p]
    have he : (-2 * Real.pi * ((2 * Real.pi)⁻¹ * inner ℝ y p) : ℝ) = -inner ℝ y p := by
      field_simp
    rw [he]
    simp only [complexify, smul_eq_mul, Complex.ofReal_neg]
    congr 2
    ring)

theorem physicalFourier_continuous (f : Space → ℝ) (hf : Integrable f (volume : Measure Space)) :
    Continuous (physicalFourier f) := by
  have hc : Integrable (complexify f) (volume : Measure Space) :=
    Complex.ofRealCLM.integrable_comp hf
  have hF : Continuous (𝓕 (complexify f)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by change Continuous (fun p : Space × Space => inner ℝ p.1 p.2); fun_prop) hc
  change Continuous (fun p : Space => (2 * Real.pi) ^ (-(3 / 2 : ℝ)) •
    𝓕 (complexify f) ((2 * Real.pi)⁻¹ • p))
  have hs : Continuous (fun p : Space => (2 * Real.pi)⁻¹ • p) := by fun_prop
  exact (continuous_const : Continuous (fun _ : Space => (2 * Real.pi) ^ (-(3 / 2 : ℝ)))).smul
    (hF.comp hs)

/-- The exponent and prefactor of the continuum manuscript, in its unitary convention. -/
theorem well_fourier_tail (R : ℝ) :
    (∫ p in {p : Space | R ≤ ‖p‖}, ‖physicalFourier w p‖ + ‖physicalFourier qw p‖) ≤
      (2 : ℝ) ^ 100 * Real.exp (-Real.sqrt R / 512) :=
  sqrt_decay_tail _ (fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
    well_physicalFourier_decay R

theorem well_physicalFourier_integrable :
    Integrable (fun p => ‖physicalFourier w p‖ + ‖physicalFourier qw p‖) (volume : Measure Space) := by
  have hc : Continuous (fun p => ‖physicalFourier w p‖ + ‖physicalFourier qw p‖) :=
    (physicalFourier_continuous w w_integrable).norm.add
      (physicalFourier_continuous qw qw_integrable).norm
  apply (tailMajorant_integrable.const_mul ((2 : ℝ) ^ 20)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    apply (well_physicalFourier_decay p).trans
    change (2 : ℝ) ^ 20 * Real.exp (-Real.sqrt ‖p‖ / 256) ≤
      (2 : ℝ) ^ 20 * Real.exp (-Real.sqrt ‖p‖ / 512)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith [Real.sqrt_nonneg ‖p‖])

end Maxwell.Continuum.Well
