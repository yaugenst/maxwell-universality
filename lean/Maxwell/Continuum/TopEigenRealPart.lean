import Maxwell.Continuum.TopEigenDataTransport

/-! A real representative of a simple eigenmode obtained from its real
part. The comparison reference is only required to be real, not normalized. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation

open NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def realPart (J : H →L[ℝ] H) (f : H) : H := (1 / 2 : ℝ) • (f + J f)

def normalizedRealPart (J : H →L[ℝ] H) (f : H) : H :=
  NormedSpace.normalize (realPart J f)

theorem realPart_fixed (J : H →L[ℝ] H) (hJ : ∀ x, J (J x) = x) (f : H) :
    J (realPart J f) = realPart J f := by
  simp only [realPart, map_smul, map_add, hJ]
  rw [add_comm (J f) f]

theorem realPart_reference_error (J : H →L[ℝ] H) (hn : ∀ x, ‖J x‖ = ‖x‖)
    (f r : H) (hr : J r = r) : ‖realPart J f - r‖ ≤ ‖f - r‖ := by
  have he : realPart J f - r = (1 / 2 : ℝ) • ((f - r) + J (f - r)) := by
    rw [map_sub, hr]
    unfold realPart
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have ht := norm_add_le (f - r) (J (f - r))
  rw [hn] at ht
  linarith

theorem realPart_original_error (J : H →L[ℝ] H) (hn : ∀ x, ‖J x‖ = ‖x‖)
    (f r : H) (hr : J r = r) : ‖realPart J f - f‖ ≤ ‖f - r‖ := by
  have he : realPart J f - f = (1 / 2 : ℝ) • (J (f - r) - (f - r)) := by
    rw [map_sub, hr]
    unfold realPart
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have ht := norm_sub_le (J (f - r)) (f - r)
  rw [hn] at ht
  linarith

theorem realPart_ne_zero (J : H →L[ℝ] H) (hn : ∀ x, ‖J x‖ = ‖x‖)
    (f r : H) (hf : ‖f‖ = 1) (hr : J r = r) (he : ‖f - r‖ < 1) :
    realPart J f ≠ 0 := by
  intro hz
  have hb := realPart_original_error J hn f r hr
  rw [hz, zero_sub, norm_neg, hf] at hb
  linarith

theorem normalizedRealPart_fixed (J : H →L[ℝ] H) (hJ : ∀ x, J (J x) = x) (f : H) :
    J (normalizedRealPart J f) = normalizedRealPart J f := by
  unfold normalizedRealPart NormedSpace.normalize
  rw [map_smul, realPart_fixed J hJ f]

theorem normalizedRealPart_error (J : H →L[ℝ] H) (hn : ∀ x, ‖J x‖ = ‖x‖)
    (f r : H) (hf : ‖f‖ = 1) (hr : J r = r) (he : ‖f - r‖ < 1) :
    ‖normalizedRealPart J f - r‖ ≤ 2 * ‖f - r‖ := by
  have hw := realPart_ne_zero J hn f r hf hr he
  have hnorm := norm_normalize hw
  change ‖normalizedRealPart J f‖ = 1 at hnorm
  have hid : normalizedRealPart J f - realPart J f =
      (1 - ‖realPart J f‖) • normalizedRealPart J f := by
    rw [sub_smul, one_smul]
    exact congrArg (fun x => normalizedRealPart J f - x)
      (norm_smul_normalize (realPart J f)).symm
  have h₁ : ‖normalizedRealPart J f - realPart J f‖ ≤ ‖realPart J f - f‖ := by
    rw [hid, norm_smul, hnorm, mul_one, Real.norm_eq_abs, abs_sub_comm]
    simpa only [hf] using abs_norm_sub_norm_le (realPart J f) f
  have ht := norm_sub_le_norm_sub_add_norm_sub (normalizedRealPart J f) (realPart J f) r
  linarith [realPart_original_error J hn f r hr, realPart_reference_error J hn f r hr]

namespace Data

variable {A : H →L[ℂ] H} {u : H} {mu d : ℝ} (D : Data A u mu d)

include D

theorem replace_unit_eigenvector (v : H) (hv : ‖v‖ = 1)
    (he : A v = (mu : ℂ) • v) : Data A v mu d where
  unit_norm := hv
  symmetric := D.symmetric
  eigenvector := he
  gap_pos := D.gap_pos
  gap_le_mu := D.gap_le_mu
  complement := by
    intro f hf
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
    have hs := D.eigenvector_simple v he
    have hc : inner ℂ u v ≠ 0 := by
      intro hz
      rw [hz, zero_smul] at hs
      exact hv0 hs
    rw [hs, inner_smul_left] at hf
    exact D.complement f ((mul_eq_zero.mp hf).resolve_left (by
      change star (inner ℂ u v) ≠ 0
      exact star_ne_zero.mpr hc))

theorem realPart_eigen (J : H →L[ℝ] H)
    (hcomm : ∀ x, A (J x) = J (A x)) :
    A (realPart J u) = (mu : ℂ) • realPart J u := by
  have hJu : A (J u) = (mu : ℂ) • J u := by
    rw [hcomm, D.eigenvector]
    change J ((algebraMap ℝ ℂ mu) • u) = (algebraMap ℝ ℂ mu) • J u
    rw [algebraMap_smul, map_smul, algebraMap_smul]
  rw [realPart, ContinuousLinearMap.map_smul_of_tower, map_add, D.eigenvector, hJu]
  module

theorem normalizedRealPart_data (J : H →L[ℝ] H)
    (hcomm : ∀ x, A (J x) = J (A x)) (hu : realPart J u ≠ 0) :
    Data A (normalizedRealPart J u) mu d := by
  apply D.replace_unit_eigenvector _ (norm_normalize hu)
  unfold NormedSpace.normalize
  rw [ContinuousLinearMap.map_smul_of_tower, D.realPart_eigen J hcomm]
  exact smul_comm _ _ _

end Data
end Maxwell.Continuum.TopEigenPerturbation
