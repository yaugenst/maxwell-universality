import Maxwell.Continuum.EffectiveMassRealMode
import Maxwell.Continuum.EffectiveMassStartingOverlap

/-! The quantitative effective-mass conclusion for the literal continuum
operator, including the prescribed starting vector and global H¹ mode. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary

attribute [local irreducible] Sh realMode muH referencePhysicalMode startingVector
  Bloch.unitary Auxiliary.resolvent

theorem realMode_starting_overlap {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    1 / (2 : ℝ)^48 ≤ (inner ℂ (startingVector D.h_pos) (realMode D hh)).re := by
  apply startingVector_overlap_of_spatial_error D.h_pos hh
  exact (realMode_spatial_error D hh).trans
    ((mul_le_mul_of_nonneg_left hh (by positivity)).trans (by norm_num))

theorem realMode_spatial_error_paper {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖realMode D hh - referencePhysicalMode D.h_pos‖ ≤ (2 : ℝ)^2048 * h :=
  (realMode_spatial_error D hh).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 921 ≤ 2048)) D.h_pos.le)

theorem realMode_simple {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (f : FieldL2)
    (hf : Sh D f = (muH D hh : ℂ) • f) :
    f = inner ℂ (realMode D hh) f • realMode D hh :=
  (realModeData D hh).eigenvector_simple f hf

/-- Every field is a conclusion about the constructed continuum operator
and the actual normalized periodic starting vector. -/
structure Conclusion {h z : ℝ} (D : Calibration h z) (μ : ℝ) (u : FieldL2) : Prop where
  unit_norm : ‖u‖ = 1
  real : fieldConjugation u = u
  eigenvector : Sh D u = (μ : ℂ) • u
  eigenvalue_bounds : (1 / (2 : ℝ)^128) * (h ^ 2)⁻¹ ≤ μ ∧
    μ ≤ (1 / (2 : ℝ)^90) * (h ^ 2)⁻¹
  mem_spectrum : (μ : ℂ) ∈ spectrum ℂ (Sh D)
  spectrum_gap : ∀ w : ℂ, w ∈ spectrum ℂ (Sh D) → w ≠ (μ : ℂ) →
    (1 / (2 : ℝ)^192) * (h ^ 2)⁻¹ ≤ dist w (μ : ℂ)
  largest : ∀ t : ℝ, (t : ℂ) ∈ spectrum ℂ (Sh D) → t ≤ μ
  simple : ∀ f : FieldL2, Sh D f = (μ : ℂ) • f → f = inner ℂ u f • u
  spatial_error : ‖u - referencePhysicalMode D.h_pos‖ ≤ (2 : ℝ)^2048 * h
  starting_overlap : 1 / (2 : ℝ)^48 ≤ (inner ℂ (startingVector D.h_pos) u).re
  supported : ∀ j : Fin 3, ∀ᵐ x ∂(volume : Measure Space), h⁻¹ ≤ ‖x‖ → u j x = 0
  sobolev : ∃ v : FourierSobolev.H1Data u, v.norm ≤ (2 : ℝ)^512 * (h ^ 2)⁻¹

theorem effectiveMass {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : Conclusion D (muH D hh) (realMode D hh) where
  unit_norm := realMode_norm D hh
  real := realMode_real D hh
  eigenvector := realMode_eigen D hh
  eigenvalue_bounds := muH_bounds D hh
  mem_spectrum := muH_mem_spectrum D hh
  spectrum_gap := muH_spectrum_gap D hh
  largest := muH_largest D hh
  simple := realMode_simple D hh
  spatial_error := realMode_spatial_error_paper D hh
  starting_overlap := realMode_starting_overlap D hh
  supported := realMode_supported D hh
  sobolev := ⟨realModeH1 D hh, realModeH1_norm_le D hh⟩

theorem exists_effectiveMass {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : ∃ μ : ℝ, ∃ u : FieldL2, Conclusion D μ u :=
  ⟨muH D hh, realMode D hh, effectiveMass D hh⟩

end Maxwell.Continuum.EffectiveMass
