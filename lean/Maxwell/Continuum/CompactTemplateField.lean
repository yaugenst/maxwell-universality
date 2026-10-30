import Maxwell.Continuum.CompactTemplateL2

/-! The three actual L2 components represented by the finite tensor arrays. -/

namespace Maxwell.Continuum.Profile

open MeasureTheory

theorem field_norm_le_sum_components (f : FieldL2) : ‖f‖≤∑ i, ‖f i‖ := by
  have hs := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ScalarL2) f
  rw [Fin.sum_univ_three] at hs ⊢
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h01 := mul_nonneg (norm_nonneg (f 0)) (norm_nonneg (f 1))
  have h02 := mul_nonneg (norm_nonneg (f 0)) (norm_nonneg (f 2))
  have h12 := mul_nonneg (norm_nonneg (f 1)) (norm_nonneg (f 2))
  nlinarith only [hs,h01,h02,h12]

variable {ι : Type*} {B : ℕ}

noncomputable def templateCoefficientMass (s : Finset ι) (a : ι → Fin 3 → ComplexDyadic B) : ℝ :=
  ∑ k, ∑ ν ∈ s, ‖complexDyadicValue (a ν k)‖

theorem templateCoefficientMass_nonneg (s : Finset ι) (a : ι → Fin 3 → ComplexDyadic B) :
    0≤templateCoefficientMass s a := by unfold templateCoefficientMass; positivity

noncomputable def encodedTemplateField (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0<L) (r : Space) : FieldL2 :=
  WithLp.toLp 2 (fun k => encodedTemplateL2 s q (fun ν => a ν k) Q N hL r)

noncomputable def idealTemplateField (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) {L : ℝ} (hL : 0<L) (r : Space) : FieldL2 :=
  WithLp.toLp 2 (fun k => idealTemplateL2 s q (fun ν => a ν k) hL r)

theorem templateField_error (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i|≤Q)
    {L : ℝ} (hL : 1≤L) (r : Space) :
    ‖idealTemplateField s q a (zero_lt_one.trans_le hL) r-
      encodedTemplateField s q a Q N (zero_lt_one.trans_le hL) r‖≤
      3*L^2*templateCoefficientMass s a*(1/2 : ℝ)^(N+22) := by
  apply (field_norm_le_sum_components _).trans
  rw [templateCoefficientMass, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  exact templateL2_error s q (fun ν => a ν k) Q N hq hL r

theorem encodedTemplateField_ae (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0<L) (r : Space) (k : Fin 3) :
    encodedTemplateField s q a Q N hL r k =ᵐ[volume] encodedPlacedTemplate s q (fun ν => a ν k) Q N L r :=
  MemLp.coeFn_toLp (encodedPlacedTemplate_memLp s q (fun ν => a ν k) Q N hL r)

theorem idealTemplateField_ae (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) {L : ℝ} (hL : 0<L) (r : Space) (k : Fin 3) :
    idealTemplateField s q a hL r k =ᵐ[volume] idealPlacedTemplate s q (fun ν => a ν k) L r :=
  MemLp.coeFn_toLp (idealPlacedTemplate_memLp s q (fun ν => a ν k) hL r)

theorem encodedTemplateField_supported (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0<L) (r : Space) (k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), L≤‖x-r‖ → encodedTemplateField s q a Q N hL r k x=0 := by
  filter_upwards [encodedTemplateField_ae s q a Q N hL r k] with x hx hxr
  rw [hx]
  exact encodedPlacedTemplate_zero s q (fun ν => a ν k) Q N hL r x hxr

theorem idealTemplateField_supported (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) {L : ℝ} (hL : 0<L) (r : Space) (k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), L≤‖x-r‖ → idealTemplateField s q a hL r k x=0 := by
  filter_upwards [idealTemplateField_ae s q a hL r k] with x hx hxr
  rw [hx]
  exact idealPlacedTemplate_zero s q (fun ν => a ν k) hL r x hxr

theorem templateField_precision (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → Fin 3 → ComplexDyadic B) (Q N ell A : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i|≤Q)
    {L : ℝ} (hL : 1≤L) (hsize : L≤(2 : ℝ)^ell) (hmass : templateCoefficientMass s a≤(2 : ℝ)^A)
    (r : Space) :
    ‖idealTemplateField s q a (zero_lt_one.trans_le hL) r-
      encodedTemplateField s q a Q (N+2*ell+A) (zero_lt_one.trans_le hL) r‖≤(1/2 : ℝ)^(N+20) := by
  apply (templateField_error s q a Q (N+2*ell+A) hq hL r).trans
  have hm0 := templateCoefficientMass_nonneg s a
  calc
    _ ≤ 3*((2 : ℝ)^ell)^2*(2 : ℝ)^A*(1/2 : ℝ)^((N+2*ell+A)+22) := by
      gcongr
    _ = 3*(1/2 : ℝ)^(N+22) := by
      have hc : (2 : ℝ)^(2*ell+A)*(1/2 : ℝ)^(2*ell+A)=1 := by rw [← mul_pow]; norm_num
      rw [← pow_mul, show ell*2=2*ell by omega,
        mul_assoc 3 ((2 : ℝ)^(2*ell)) ((2 : ℝ)^A), ← pow_add,
        show (N+2*ell+A)+22=(2*ell+A)+(N+22) by omega, pow_add]
      calc
        _ = 3*((2 : ℝ)^(2*ell+A)*(1/2 : ℝ)^(2*ell+A))*(1/2 : ℝ)^(N+22) := by ring
        _ = _ := by rw [hc, mul_one]
    _ ≤ _ := by
      rw [show N+22=(N+20)+2 by omega, pow_add]
      nlinarith only [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) (N+20)]

#print axioms templateField_error
#print axioms templateField_precision

end Maxwell.Continuum.Profile
