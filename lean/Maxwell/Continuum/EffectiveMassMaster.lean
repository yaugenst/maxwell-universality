import Maxwell.Continuum.EffectiveMassTheorem
import Maxwell.Continuum.MasterConstants

/-! The effective-mass lemma at the manuscript's explicit master length.
The energy enclosure is the input to calibration; no spectral,
eigenfunction, approximation or regularity property is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary FreeFiber MasterConstants

attribute [local irreducible] Sh realMode muH referencePhysicalMode startingVector
  Bloch.unitary Auxiliary.resolvent Cs Ls

theorem effectiveMass_of_length {L z : ℝ} (hL : Ls ≤ L)
    (hz : |z - (centerEnergy - (L⁻¹)^2)| ≤ (L⁻¹)^4) :
    Conclusion (calibration_of_length hL hz)
      (muH (calibration_of_length hL hz) (inverse_length_le_1024 hL))
      (realMode (calibration_of_length hL hz) (inverse_length_le_1024 hL)) :=
  effectiveMass (calibration_of_length hL hz) (inverse_length_le_1024 hL)

/-- The actual continuum effective-mass theorem, with the displayed
length, gap, error, sign and H¹ constants. -/
theorem exists_effectiveMass_length {L z : ℝ} (hL : Ls ≤ L)
    (hz : |z - (centerEnergy - (L⁻¹)^2)| ≤ (L⁻¹)^4) :
    let D := calibration_of_length hL hz
    ∃ μ : ℝ, ∃ u : FieldL2,
      ‖u‖ = 1 ∧
      fieldConjugation u = u ∧
      Sh D u = (μ : ℂ) • u ∧
      ((1 / (2 : ℝ)^128) * L^2 ≤ μ ∧ μ ≤ (1 / (2 : ℝ)^90) * L^2) ∧
      (μ : ℂ) ∈ spectrum ℂ (Sh D) ∧
      (∀ w : ℂ, w ∈ spectrum ℂ (Sh D) → w ≠ (μ : ℂ) →
        (1 / (2 : ℝ)^192) * L^2 ≤ dist w (μ : ℂ)) ∧
      (∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ (Sh D) → t ≤ μ) ∧
      (∀ f : FieldL2, Sh D f = (μ : ℂ) • f → f = inner ℂ u f • u) ∧
      (‖u - referencePhysicalMode D.h_pos‖ ≤ (2 : ℝ)^2048 * L⁻¹ ∧
        (2 : ℝ)^2048 * L⁻¹ ≤ Cs * L⁻¹) ∧
      (1 / (2 : ℝ)^48 ≤ (inner ℂ (startingVector D.h_pos) u).re) ∧
      (∀ j : Fin 3, ∀ᵐ x ∂(volume : Measure Space), L ≤ ‖x‖ → u j x = 0) ∧
      (∃ v : FourierSobolev.H1Data u,
        v.norm ≤ (2 : ℝ)^512 * L^2 ∧ (2 : ℝ)^512 * L^2 ≤ Cs * L^2) := by
  let D := calibration_of_length hL hz
  let hh := inverse_length_le_1024 hL
  have ht := effectiveMass D hh
  refine ⟨muH D hh, realMode D hh, ht.unit_norm, ht.real, ht.eigenvector,
    ?_, ht.mem_spectrum, ?_, ht.largest, ht.simple, ?_, ht.starting_overlap, ?_, ?_⟩
  · simpa only [inv_pow, inv_inv] using ht.eigenvalue_bounds
  · intro w hw hne
    simpa only [inv_pow, inv_inv] using ht.spectrum_gap w hw hne
  · exact ⟨ht.spatial_error,
      mul_le_mul_of_nonneg_right spatial_constant_le_Cs (inverse_length_pos hL).le⟩
  · intro j
    simpa only [inv_inv] using ht.supported j
  · obtain ⟨v, hv⟩ := ht.sobolev
    refine ⟨v, ?_, mul_le_mul_of_nonneg_right H1_constant_le_Cs (sq_nonneg L)⟩
    simpa only [inv_pow, inv_inv] using hv

end Maxwell.Continuum.EffectiveMass
