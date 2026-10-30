import Maxwell.Continuum.FiniteAuxiliarySourceEncoding
import Maxwell.Continuum.FiniteAuxiliaryMessageFormat

/-! The same compact encoded templates serve the source and the volume
readouts. Their disjoint physical supports remove every site-count
factor from the readout operator error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open MeasureTheory EffectiveMass Auxiliary MasterConstants

variable {ι : Type*} [Fintype ι]

theorem encodedReadout_error {L z e : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (he : 0 ≤ e) (r : ι → Space)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ (2 : ℝ)^130*L⁻¹^2)
    (a : ι → FieldL2)
    (hsa : ∀ i k, ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) L → a i k x = 0)
    (ha : ∀ i, ‖a i-siteInsertion L⁻¹ (r i) (realMode D (inverse_length_le_1024 hL))‖ ≤ e) :
    ‖weightedTemplateReadout v a-
      idealReadout L⁻¹ r v (realMode D (inverse_length_le_1024 hL))‖ ≤ e := by
  let b := fun i => siteInsertion L⁻¹ (r i) (realMode D (inverse_length_le_1024 hL))
  have hb (i : ι) (k : Fin 3) : ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) L → b i k x = 0 := by
    rw [show b i = Bloch.fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL)) from rfl]
    apply translated_supported_ball
    intro j
    simpa only [inv_inv] using actualSource_supported D (inverse_length_le_1024 hL) j
  have ht := weightedTemplateReadout_error
    (show 0 ≤ (2 : ℝ)^130*L⁻¹^2 by positivity) he v hv a b ha
    (fun i => Metric.ball (r i) L) hdisj
    (fun i => field_difference_supported _ _ _ (hsa i) (hb i))
  rw [weightedTemplateReadout_ideal] at ht
  exact ht.trans ((mul_le_mul_of_nonneg_right (readout_strength_budget hL) he).trans_eq (one_mul e))

theorem weighted_template_round_error (P : ℕ) (v w : ι → ℚ) (a : ι → FieldL2)
    (E : FieldL2) {δ : ℝ} (hv : ∀ i, |(v i : ℝ)| ≤ 1)
    (hw : ∀ i, |(w i : ℝ)-(inner ℂ (a i) E).re| ≤ δ)
    (hP : (1/2 : ℝ)^P ≤ δ) (i : ι) :
    |((roundDyadic P (v i*w i)).value : ℝ)-
      (weightedTemplateReadout (fun j => (v j : ℝ)) a E i).re| ≤ 2*δ := by
  rw [weightedTemplateReadout_apply]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    weighted_round_error P (v i) (w i) (hv i) (hw i) hP

#print axioms encodedReadout_error
#print axioms weighted_template_round_error

end Maxwell.Continuum.FiniteAuxiliary
