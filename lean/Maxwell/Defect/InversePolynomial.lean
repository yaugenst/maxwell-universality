import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Finite inverse polynomials for the exact fixed-platform checker. -/

namespace Maxwell.Defect

section Algebra
variable {𝕜 A : Type*} [CommRing 𝕜] [Ring A] [Algebra 𝕜 A]

/-- For `s=1/M²` this is the finite-propagation inverse polynomial in the
fixed-search specification. It uses only finite ring operations. -/
def inversePolynomial (H : A) (s : 𝕜) (N : ℕ) : A :=
  (s • H) * ∑ j ∈ Finset.range (N + 1), (1 - s • H ^ 2) ^ j

theorem inversePolynomial_residual (H : A) (s : 𝕜) (N : ℕ) :
    H * inversePolynomial H s N = 1 - (1 - s • H ^ 2) ^ (N + 1) := by
  unfold inversePolynomial
  rw [← mul_assoc, mul_smul_comm, ← pow_two]
  have hcancel : (1 : A) - (1 - s • H ^ 2) = s • H ^ 2 := sub_sub_cancel _ _
  have h := mul_neg_geom_sum (1 - s • H ^ 2) (N + 1)
  rw [hcancel] at h
  exact h

theorem inversePolynomial_error_identity (H X : A) (s : 𝕜) (N : ℕ) (hX : X * H = 1) :
    X - inversePolynomial H s N = X * (1 - s • H ^ 2) ^ (N + 1) := by
  have h := congrArg (fun a => X * a) (inversePolynomial_residual H s N)
  rw [← mul_assoc, hX, one_mul, mul_sub, mul_one] at h
  rw [h]
  noncomm_ring

/-- Real/rational scalar inverse polynomials preserve self-adjointness,
including in the infinite-dimensional noncommutative operator algebra. -/
theorem inversePolynomial_selfAdjoint [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A]
    (H : A) (s : 𝕜) (N : ℕ) (hH : IsSelfAdjoint H) (hs : IsSelfAdjoint s) :
    IsSelfAdjoint (inversePolynomial H s N) := by
  have hc : Commute H (1 - s • H ^ 2) :=
    (Commute.one_right H).sub_right ((Commute.refl H).pow_right 2 |>.smul_right s)
  have hsum : Commute (s • H) (∑ j ∈ Finset.range (N + 1), (1 - s • H ^ 2) ^ j) :=
    (Commute.sum_right _ _ H (fun j _ => hc.pow_right j)).smul_left s
  change star (inversePolynomial H s N) = inversePolynomial H s N
  simp only [inversePolynomial, star_mul, star_sum, star_pow, star_sub,
    star_one, star_smul, hH.star_eq, hs.star_eq]
  exact hsum.eq.symm

end Algebra

section Norm
variable {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A]

theorem inversePolynomial_error_bound (H X : A) (s : ℝ) (N : ℕ)
    (hX : X * H = 1) {δ r : ℝ} (hδ : 0 < δ)
    (hinv : ‖X‖ ≤ δ⁻¹) (hcontraction : ‖1 - s • H ^ 2‖ ≤ r) :
    ‖X - inversePolynomial H s N‖ ≤ δ⁻¹ * r ^ (N + 1) := by
  rw [inversePolynomial_error_identity H X s N hX]
  apply (norm_mul_le _ _).trans
  apply mul_le_mul hinv _ (norm_nonneg _) (inv_pos.mpr hδ).le
  exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hcontraction _)

/-- Every positive requested error has a finite polynomial degree; a
candidate cannot require an infinite-volume numerical inversion oracle. -/
theorem exists_inversePolynomial_precision (H X : A) (s : ℝ) (hX : X * H = 1)
    {δ r ε : ℝ} (hδ : 0 < δ) (hr : 0 ≤ r) (hr1 : r < 1) (hε : 0 < ε)
    (hinv : ‖X‖ ≤ δ⁻¹) (hcontraction : ‖1 - s • H ^ 2‖ ≤ r) :
    ∃ N, ‖X - inversePolynomial H s N‖ < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos hε hδ) hr1
  have hstep : r ^ (N + 1) ≤ r ^ N := by
    rw [pow_succ]
    nlinarith [pow_nonneg hr N]
  have hbound := inversePolynomial_error_bound H X s N hX hδ hinv hcontraction
  refine ⟨N, lt_of_le_of_lt hbound ?_⟩
  have hN' : r ^ (N + 1) < ε * δ := hstep.trans_lt hN
  have := mul_lt_mul_of_pos_left hN' (inv_pos.mpr hδ)
  have hcancel : δ⁻¹ * (ε * δ) = ε := by
    rw [mul_left_comm, inv_mul_cancel₀ hδ.ne', mul_one]
  rwa [hcancel] at this

end Norm

end Maxwell.Defect
