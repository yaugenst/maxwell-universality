import Maxwell.Continuum.CompactTemplateReal

/-! The original finite tensor precision budget applies unchanged to
real output templates, including approximation of an actual real L² field. -/

namespace Maxwell.Continuum.Profile

open MeasureTheory

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

attribute [local irreducible] encodedTemplateField idealTemplateField

variable {ι : Type*} {B : ℕ}

theorem realEncodedTemplateField_precision (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N ell A : ℕ)
    (hq : ∀ ν ∈ s, ∀ i, |q ν i| ≤ Q)
    {L : ℝ} (hL : 1 ≤ L) (hsize : L ≤ (2 : ℝ)^ell)
    (hmass : templateCoefficientMass s a ≤ (2 : ℝ)^A) (r : Space)
    (g : FieldL2) (hg : fieldConjugation g = g) :
    ‖realEncodedTemplateField s q a Q (N+2*ell+A) (zero_lt_one.trans_le hL) r-g‖ ≤
      ‖idealTemplateField s q a (zero_lt_one.trans_le hL) r-g‖+(1/2 : ℝ)^(N+20) := by
  let f := encodedTemplateField s q a Q (N+2*ell+A) (zero_lt_one.trans_le hL) r
  let f₀ := idealTemplateField s q a (zero_lt_one.trans_le hL) r
  have he := templateField_precision s q a Q N ell A hq hL hsize hmass r
  rw [norm_sub_rev] at he
  change ‖f-f₀‖ ≤ (1/2 : ℝ)^(N+20) at he
  change ‖fieldRealProjection f-g‖ ≤ _
  calc
    _ ≤ ‖f-g‖ := fieldRealProjection_error f hg
    _ ≤ ‖f-f₀‖+‖f₀-g‖ := norm_sub_le_norm_sub_add_norm_sub f f₀ g
    _ ≤ (1/2 : ℝ)^(N+20)+‖f₀-g‖ := add_le_add he le_rfl
    _ = _ := add_comm _ _

#print axioms realEncodedTemplateField_precision

end Maxwell.Continuum.Profile
