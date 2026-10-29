import Maxwell.Continuum.SelfAdjointResolventData
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Spectral distance controls the actual unbounded resolvent

The proof uses only the bounded self-adjoint spectral norm theorem. A nonzero
spectral value of a bounded resolvent maps to a spectral value of the original
partial operator. Thus the quantitative estimate does not assume a lower
norm bound or the existence of a solution to an equation.
-/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Resolvent identities give an explicit inverse for the bounded shift factor. -/
theorem resolvent_factor_mul (A : H →ₗ.[ℂ] H) (σ τ : ℝ)
    (R : BoundedInverse (shift A σ)) (S : BoundedInverse (shift A τ)) :
    (1 - (τ - σ) • R.map) * (1 + (τ - σ) • S.map) = 1 ∧
      (1 + (τ - σ) • S.map) * (1 - (τ - σ) • R.map) = 1 := by
  have hRS : S.map - R.map = (τ - σ) • (R.map * S.map) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact resolvent_identity A σ τ R S
  have hSR : S.map - R.map = (τ - σ) • (S.map * R.map) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact resolvent_identity_reverse A σ τ R S
  constructor
  · calc
      (1 - (τ - σ) • R.map) * (1 + (τ - σ) • S.map) =
          1 + (τ - σ) • (S.map - R.map - (τ - σ) • (R.map * S.map)) := by
        simp only [mul_add, sub_mul, mul_one, one_mul, mul_smul_comm,
          smul_mul_assoc, smul_sub, smul_smul]
        abel
      _ = 1 := by rw [← hRS, sub_self, smul_zero, add_zero]
  · calc
      (1 + (τ - σ) • S.map) * (1 - (τ - σ) • R.map) =
          1 + (τ - σ) • (S.map - R.map - (τ - σ) • (S.map * R.map)) := by
        simp only [mul_sub, add_mul, mul_one, one_mul, mul_smul_comm,
          smul_mul_assoc, smul_sub, smul_add, smul_smul]
        abel
      _ = 1 := by rw [← hSR, sub_self, smul_zero, add_zero]

/-- A nonzero bounded-resolvent spectral value maps into the spectrum of
the genuinely unbounded partial operator. -/
theorem inverse_spectral_transfer (A : H →ₗ.[ℂ] H) (σ : ℝ)
    (R : BoundedInverse (shift A σ)) {r : ℝ} (hr : r ≠ 0)
    (hrspec : r ∈ spectrum ℝ R.map) : σ + r⁻¹ ∈ realSpectrum A := by
  by_contra h
  obtain ⟨S⟩ := (not_mem_realSpectrum A (σ + r⁻¹)).mp h
  have hf := resolvent_factor_mul A σ (σ + r⁻¹) R S
  simp only [add_sub_cancel_left] at hf
  have hfactor : algebraMap ℝ (H →L[ℂ] H) r - R.map = r • (1 - r⁻¹ • R.map) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, mul_inv_cancel₀ hr, one_smul]
  have hres : r ∈ resolventSet ℝ R.map := by
    apply spectrum.mem_resolventSet_of_left_right_inverse
      (b := r⁻¹ • (1 + r⁻¹ • S.map)) (c := r⁻¹ • (1 + r⁻¹ • S.map))
    · rw [hfactor, smul_mul_smul_comm, mul_inv_cancel₀ hr, one_smul, hf.1]
    · rw [hfactor, smul_mul_smul_comm, inv_mul_cancel₀ hr, one_smul, hf.2]
  exact hrspec hres

variable [CompleteSpace H]

/-- The exact `1 / δ` L² bound follows from actual spectral exclusion. -/
theorem boundedInverse_norm_le_of_gap (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (σ : ℝ) (R : BoundedInverse (shift A σ)) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ lam ∈ realSpectrum A, δ ≤ |σ - lam|) : ‖R.map‖ ≤ δ⁻¹ := by
  by_cases hnorm : ‖R.map‖ = 0
  · rw [hnorm]
    positivity
  have hpos : 0 < ‖R.map‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnorm)
  let : Nontrivial (H →L[ℂ] H) := nontrivial_of_ne R.map 0 (norm_ne_zero_iff.mp hnorm)
  have hR := R.map_selfAdjoint (shift_selfAdjoint A σ hA)
  obtain ⟨r, hrspec, habs⟩ : ∃ r : ℝ, r ∈ spectrum ℝ R.map ∧ |r| = ‖R.map‖ := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum R.map hR with hp | hn
    · exact ⟨‖R.map‖, hp, abs_of_nonneg (norm_nonneg _)⟩
    · exact ⟨-‖R.map‖, hn, by rw [abs_neg, abs_of_nonneg (norm_nonneg _)]⟩
  have hr : r ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at habs
    exact hpos.ne' habs.symm
  have hd := hgap (σ + r⁻¹) (inverse_spectral_transfer A σ R hr hrspec)
  have he : |σ - (σ + r⁻¹)| = ‖R.map‖⁻¹ := by
    rw [show σ - (σ + r⁻¹) = -r⁻¹ by ring, abs_neg, abs_inv, habs]
  rw [he] at hd
  exact (le_inv_comm₀ hδ hpos).mp hd

/-- Outside the actual spectrum, a spectral gap constructs a two-sided
bounded inverse with the sharp reciprocal-gap bound. -/
theorem exists_boundedInverse_of_spectral_gap (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (σ : ℝ) (hσ : σ ∉ realSpectrum A) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ lam ∈ realSpectrum A, δ ≤ |σ - lam|) :
    ∃ R : BoundedInverse (shift A σ), ‖R.map‖ ≤ δ⁻¹ := by
  obtain ⟨R⟩ := (not_mem_realSpectrum A σ).mp hσ
  exact ⟨R, boundedInverse_norm_le_of_gap A hA σ R hδ hgap⟩

/-- A positive distance from every spectral point already excludes the shift
from the spectrum, so no separate solvability hypothesis is needed. -/
theorem exists_boundedInverse_of_gap (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (σ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ lam ∈ realSpectrum A, δ ≤ |σ - lam|) :
    ∃ R : BoundedInverse (shift A σ), ‖R.map‖ ≤ δ⁻¹ := by
  apply exists_boundedInverse_of_spectral_gap A hA σ _ hδ hgap
  intro hs
  have h := hgap σ hs
  rw [sub_self, abs_zero] at h
  exact (not_le_of_gt hδ) h

/-- The norm lower bound for an unbounded self-adjoint operator is a
consequence of spectral separation, not an additional assumption. -/
theorem lower_bound_of_spectral_gap (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (σ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ lam ∈ realSpectrum A, δ ≤ |σ - lam|) (x : A.domain) :
    δ * ‖(x : H)‖ ≤ ‖A x - (σ : ℂ) • (x : H)‖ := by
  obtain ⟨R, hR⟩ := exists_boundedInverse_of_gap A hA σ hδ hgap
  have hnorm : ‖(x : H)‖ ≤ δ⁻¹ * ‖shift A σ x‖ := by
    calc
      ‖(x : H)‖ = ‖R.map (shift A σ x)‖ := congrArg norm (R.map_apply x).symm
      _ ≤ ‖R.map‖ * ‖shift A σ x‖ := R.map.le_opNorm _
      _ ≤ δ⁻¹ * ‖shift A σ x‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
  have h := mul_le_mul_of_nonneg_left hnorm hδ.le
  convert! h using 1
  simp only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hδ), one_mul, shift_apply]
  rfl

end Maxwell.Continuum.SelfAdjointResolvent
