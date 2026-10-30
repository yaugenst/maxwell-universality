import Maxwell.Continuum.FourierConjugationNorm

/-! The literal real-part projection on physical L² fields. It is a
contraction and preserves compact support and approximation to real fields. -/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory

def fieldRealProjection : FieldL2 →L[ℝ] FieldL2 :=
  (1/2 : ℝ) • (1+fieldConjugation)

theorem fieldRealProjection_apply (f : FieldL2) :
    fieldRealProjection f = (1/2 : ℝ) • (f+fieldConjugation f) := rfl

theorem fieldRealProjection_norm (f : FieldL2) : ‖fieldRealProjection f‖ ≤ ‖f‖ := by
  rw [fieldRealProjection_apply, norm_smul]
  have h := norm_add_le f (fieldConjugation f)
  rw [fieldConjugation_norm] at h
  norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  linarith only [h]

theorem fieldRealProjection_real (f : FieldL2) :
    fieldConjugation (fieldRealProjection f) = fieldRealProjection f := by
  rw [fieldRealProjection_apply, map_smul, map_add, fieldConjugation_involutive, add_comm]

theorem fieldRealProjection_fixed {f : FieldL2} (hf : fieldConjugation f = f) :
    fieldRealProjection f = f := by
  rw [fieldRealProjection_apply, hf, ← two_smul ℝ f, smul_smul]
  norm_num

theorem fieldRealProjection_error (f : FieldL2) {g : FieldL2}
    (hg : fieldConjugation g = g) : ‖fieldRealProjection f-g‖ ≤ ‖f-g‖ := by
  calc
    _ = ‖fieldRealProjection (f-g)‖ := by rw [map_sub, fieldRealProjection_fixed hg]
    _ ≤ _ := fieldRealProjection_norm (f-g)

theorem fieldRealProjection_ae (f : FieldL2) (k : Fin 3) :
    fieldRealProjection f k =ᵐ[volume] fun x => ((f k x).re : ℂ) := by
  filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (f k+scalarConjugation (f k)),
    Lp.coeFn_add (f k) (scalarConjugation (f k)), scalarConjugation_ae (f k)]
      with x hs ha hc
  change ((1/2 : ℝ) • (f k+scalarConjugation (f k)) : ScalarL2) x = _
  rw [hs, Pi.smul_apply, ha, Pi.add_apply, hc]
  apply Complex.ext
  · simp [Complex.real_smul]
    ring
  · simp [Complex.real_smul]

theorem fieldRealProjection_supported (f : FieldL2) (s : Set Space)
    (hf : ∀ k, ∀ᵐ x ∂(volume : Measure Space), x ∉ s → f k x = 0) (k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), x ∉ s → fieldRealProjection f k x = 0 := by
  filter_upwards [fieldRealProjection_ae f k, hf k] with x hr hs hnot
  rw [hr, hs hnot, Complex.zero_re, Complex.ofReal_zero]

theorem field_real_ae {f : FieldL2} (hf : fieldConjugation f = f) (k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), (f k x).im = 0 := by
  have h := fieldRealProjection_ae f k
  rw [fieldRealProjection_fixed hf] at h
  filter_upwards [h] with x hx
  rw [hx, Complex.ofReal_im]

#print axioms fieldRealProjection_error
#print axioms fieldRealProjection_ae

end Maxwell.Continuum
