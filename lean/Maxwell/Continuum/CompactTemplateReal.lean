import Maxwell.Continuum.CompactTemplateField
import Maxwell.Continuum.FieldRealProjection

/-! Real-valued output templates use exactly the real dyadic tensor
coefficients. Real projection loses neither support nor L² accuracy. -/

namespace Maxwell.Continuum.Profile

open MeasureTheory

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

variable {ι : Type*} {B : ℕ}

def realFourierTensorCoefficient (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (j : Fin 3 → Fin (waveDegree (8*Q) N)) :=
  (fourierTensorCoefficient s q a Q N j).1

noncomputable def realFourierTensor (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3 → Fin (waveDegree (8*Q) N),
    ((realFourierTensorCoefficient s q a Q N j).value : ℝ)*∏ i, cubeBasis (j i) (x i)

theorem realFourierTensor_eq (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (x : Fin 3 → ℝ) :
    realFourierTensor s q a Q N x = (fourierTensor s q a Q N x).re := by
  unfold realFourierTensor fourierTensor
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.ofReal_prod]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, complexDyadicValue_re, realFourierTensorCoefficient]

theorem realFourierTensorCoefficient_bound (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i| ≤ Q)
    (j : Fin 3 → Fin (waveDegree (8*Q) N)) :
    |((realFourierTensorCoefficient s q a Q N j).value : ℝ)| ≤
      (∑ ν ∈ s, ‖complexDyadicValue (a ν)‖)*22^3 := by
  have h := (Complex.abs_re_le_norm (complexDyadicValue (fourierTensorCoefficient s q a Q N j))).trans
    (fourierTensorCoefficient_norm s q a Q N hq j)
  simpa only [complexDyadicValue_re, realFourierTensorCoefficient] using h

noncomputable def realEncodedTemplate (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (y : Space) : ℝ :=
  encodedRoot N y * realFourierTensor s q a Q N (fun i => y i)

theorem realEncodedTemplate_eq (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (y : Space) :
    realEncodedTemplate s q a Q N y = (encodedTemplate s q a Q N y).re := by
  rw [realEncodedTemplate, realFourierTensor_eq, encodedTemplate]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

noncomputable def realEncodedPlacedTemplate (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (L : ℝ) (r x : Space) : ℝ :=
  realEncodedTemplate s q a Q N (L⁻¹ • (x-r))

theorem realEncodedPlacedTemplate_eq (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (L : ℝ) (r x : Space) :
    realEncodedPlacedTemplate s q a Q N L r x = (encodedPlacedTemplate s q a Q N L r x).re :=
  realEncodedTemplate_eq s q a Q N _

noncomputable def realEncodedTemplateField (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0 < L) (r : Space) : FieldL2 :=
  fieldRealProjection (encodedTemplateField s q a Q N hL r)

attribute [local irreducible] encodedTemplateField idealTemplateField

set_option backward.isDefEq.respectTransparency true

theorem realEncodedTemplateField_real (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0 < L) (r : Space) :
    fieldConjugation (realEncodedTemplateField s q a Q N hL r) =
      realEncodedTemplateField s q a Q N hL r := fieldRealProjection_real _

theorem realEncodedTemplateField_ae (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0 < L) (r : Space) (k : Fin 3) :
    realEncodedTemplateField s q a Q N hL r k =ᵐ[volume]
      fun x => (realEncodedPlacedTemplate s q (fun ν => a ν k) Q N L r x : ℂ) := by
  filter_upwards [fieldRealProjection_ae (encodedTemplateField s q a Q N hL r) k,
    encodedTemplateField_ae s q a Q N hL r k] with x hr he
  change fieldRealProjection (encodedTemplateField s q a Q N hL r) k x = _
  rw [hr, he, realEncodedPlacedTemplate_eq]

theorem realEncodedTemplateField_supported (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0 < L) (r : Space) (k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), L ≤ ‖x-r‖ →
      realEncodedTemplateField s q a Q N hL r k x = 0 := by
  filter_upwards [fieldRealProjection_ae (encodedTemplateField s q a Q N hL r) k,
    encodedTemplateField_supported s q a Q N hL r k] with x hr hs hx
  change fieldRealProjection (encodedTemplateField s q a Q N hL r) k x = _
  rw [hr, hs hx, Complex.zero_re, Complex.ofReal_zero]

theorem realEncodedTemplateField_error (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i| ≤ Q)
    {L : ℝ} (hL : 1 ≤ L) (r : Space) (g : FieldL2) (hg : fieldConjugation g = g) :
    ‖realEncodedTemplateField s q a Q N (zero_lt_one.trans_le hL) r-g‖ ≤
      ‖idealTemplateField s q a (zero_lt_one.trans_le hL) r-g‖+
      3*L^2*templateCoefficientMass s a*(1/2 : ℝ)^(N+22) := by
  let f := encodedTemplateField s q a Q N (zero_lt_one.trans_le hL) r
  let f₀ := idealTemplateField s q a (zero_lt_one.trans_le hL) r
  have he := templateField_error s q a Q N hq hL r
  rw [norm_sub_rev] at he
  change ‖f-f₀‖ ≤ 3*L^2*templateCoefficientMass s a*(1/2 : ℝ)^(N+22) at he
  change ‖fieldRealProjection f-g‖ ≤ _
  calc
    _ ≤ ‖f-g‖ := fieldRealProjection_error f hg
    _ ≤ ‖f-f₀‖+‖f₀-g‖ := norm_sub_le_norm_sub_add_norm_sub f f₀ g
    _ ≤ 3*L^2*templateCoefficientMass s a*(1/2 : ℝ)^(N+22)+‖f₀-g‖ := add_le_add he le_rfl
    _ = _ := add_comm _ _

#print axioms realFourierTensor_eq
#print axioms realEncodedTemplateField_ae
#print axioms realEncodedTemplateField_error

end Maxwell.Continuum.Profile
