import Maxwell.Continuum.CompactTemplateRealPrecision
import Maxwell.Continuum.FiniteAuxiliaryRealSource

/-! Real finite templates meet the concrete support, norm, and error
contract consumed by the actual every-field source and readout recovery. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.Profile

open MeasureTheory EffectiveMass FiniteAuxiliary

attribute [local irreducible] encodedTemplateField idealTemplateField realMode

variable {ι : Type*} {B : ℕ}

theorem realEncodedTemplate_site_error (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N ell A : ℕ)
    (hq : ∀ ν ∈ s, ∀ i, |q ν i| ≤ Q)
    {L z δ : ℝ} (hL : 1 ≤ L) (hsize : L ≤ (2 : ℝ)^ell)
    (hmass : templateCoefficientMass s a ≤ (2 : ℝ)^A)
    (D : Auxiliary.Calibration L⁻¹ z) (hh : L⁻¹ ≤ 1/(2 : ℝ)^1024) (r : Space)
    (hfinite : ‖idealTemplateField s q a (zero_lt_one.trans_le hL) r-
      siteInsertion L⁻¹ r (realMode D hh)‖ ≤ δ) :
    ‖realEncodedTemplateField s q a Q (N+2*ell+A) (zero_lt_one.trans_le hL) r-
      siteInsertion L⁻¹ r (realMode D hh)‖ ≤ δ+(1/2 : ℝ)^(N+20) := by
  exact (realEncodedTemplateField_precision s q a Q N ell A hq hL hsize hmass r _
    (ideal_template_real D hh r)).trans (add_le_add hfinite le_rfl)

theorem realEncodedTemplate_site_certificate (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N ell A : ℕ)
    (hq : ∀ ν ∈ s, ∀ i, |q ν i| ≤ Q)
    {L z δ : ℝ} (hL : 1 ≤ L) (hsize : L ≤ (2 : ℝ)^ell)
    (hmass : templateCoefficientMass s a ≤ (2 : ℝ)^A)
    (D : Auxiliary.Calibration L⁻¹ z) (hh : L⁻¹ ≤ 1/(2 : ℝ)^1024) (r : Space)
    (hfinite : ‖idealTemplateField s q a (zero_lt_one.trans_le hL) r-
      siteInsertion L⁻¹ r (realMode D hh)‖ ≤ δ)
    (hsmall : δ+(1/2 : ℝ)^(N+20) ≤ 1) :
    let f := realEncodedTemplateField s q a Q (N+2*ell+A) (zero_lt_one.trans_le hL) r
    fieldConjugation f = f ∧ ‖f‖ ≤ 2 ∧
      (∀ k, ∀ᵐ x ∂(volume : Measure Space), x ∉ Metric.ball r L → f k x = 0) ∧
      ‖f-siteInsertion L⁻¹ r (realMode D hh)‖ ≤ δ+(1/2 : ℝ)^(N+20) := by
  dsimp only
  let f := realEncodedTemplateField s q a Q (N+2*ell+A) (zero_lt_one.trans_le hL) r
  have he := realEncodedTemplate_site_error s q a Q N ell A hq hL hsize hmass D hh r hfinite
  refine ⟨realEncodedTemplateField_real _ _ _ _ _ _ _, ?_, ?_, he⟩
  · have hg : ‖siteInsertion L⁻¹ r (realMode D hh)‖ ≤ 1 := by
      have hn := (siteInsertion L⁻¹ r).le_of_opNorm_le (siteInsertion_norm L⁻¹ r) (realMode D hh)
      simpa only [realMode_norm, one_mul] using hn
    have hn := norm_sub_le_norm_sub_add_norm_sub f (siteInsertion L⁻¹ r (realMode D hh)) 0
    simp only [sub_zero] at hn
    change ‖f-siteInsertion L⁻¹ r (realMode D hh)‖ ≤ _ at he
    change ‖f‖ ≤ 2
    linarith only [hn, hg, he, hsmall]
  · intro k
    filter_upwards [realEncodedTemplateField_supported s q a Q (N+2*ell+A)
      (zero_lt_one.trans_le hL) r k] with x hx hnot
    exact hx (by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hnot)

#print axioms realEncodedTemplate_site_certificate

end Maxwell.Continuum.Profile
