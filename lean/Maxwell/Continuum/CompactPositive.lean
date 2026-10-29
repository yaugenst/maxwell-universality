import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! A nonzero compact positive operator has an actual normalized top
eigenvector. Spectral membership is derived from positivity and the
C*-norm, and compactness converts it to an eigenvalue. -/

noncomputable section

namespace Maxwell.Continuum

open Module.End

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

theorem compactPositive_topEigenvector (T : H →L[ℂ] H) (hcompact : IsCompactOperator T)
    (hpos : T.IsPositive) (hne : T ≠ 0) :
    ∃ v : H, ‖v‖ = 1 ∧ T v = (‖T‖ : ℂ) • v := by
  have hnorm : 0 < ‖T‖ := norm_pos_iff.mpr hne
  have hs : ‖T‖ ∈ spectrum ℝ T :=
    CStarAlgebra.norm_mem_spectrum_of_nonneg T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hpos)
  have hs' : (‖T‖ : ℂ) ∈ spectrum ℂ T := by
    exact spectrum.algebraMap_mem ℂ hs
  have hn : (‖T‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm.ne'
  have he := (hcompact.hasEigenvalue_iff_mem_spectrum hn).mpr hs'
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  have hvEq : T v = (‖T‖ : ℂ) • v := hv.apply_eq_smul
  refine ⟨(‖v‖⁻¹ : ℂ) • v, ?_, ?_⟩
  · simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hvn]
  · rw [map_smul, hvEq]
    exact smul_comm _ _ _

end Maxwell.Continuum
