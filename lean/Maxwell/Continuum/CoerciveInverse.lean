import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Positive bounded inverses without a spectral assumption

Coercivity constructs the inverse. A direct quadratic variational argument
proves that increasing the positive operator decreases its inverse. This is
the order estimate needed when eliminating the infinite gradient subspace.
-/

noncomputable section

namespace Maxwell.Continuum.CoerciveInverse

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def Coercive (B : H →L[ℂ] H) (c : ℝ) : Prop :=
  ∀ x, c * ‖x‖ ^ 2 ≤ (inner ℂ x (B x)).re

theorem isUnit (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) : IsUnit B := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map B
    (c := ⟨c, hc.le⟩) hc
  intro x
  change ‖x‖ ^ 2 * c ≤ ‖inner ℂ (B x) x‖
  calc
    ‖x‖ ^ 2 * c = c * ‖x‖ ^ 2 := mul_comm _ _
    _ ≤ (inner ℂ x (B x)).re := hB x
    _ ≤ ‖inner ℂ x (B x)‖ := Complex.re_le_norm _
    _ = ‖inner ℂ (B x) x‖ := norm_inner_symm _ _

/-- The inverse is constructed from coercivity, rather than supplied as data. -/
def equiv (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c) (hB : Coercive B c) : H ≃L[ℂ] H :=
  ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr
      (ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit B hc hB)).1)
    (LinearMap.range_eq_top.mpr
      (ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit B hc hB)).2)

@[simp] theorem equiv_apply (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) (x : H) : equiv B hc hB x = B x := rfl

def inverse (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c) (hB : Coercive B c) : H →L[ℂ] H :=
  (equiv B hc hB).symm.toContinuousLinearMap

@[simp] theorem apply_inverse (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) (x : H) : B (inverse B hc hB x) = x :=
  (equiv B hc hB).apply_symm_apply x

@[simp] theorem inverse_apply (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) (x : H) : inverse B hc hB (B x) = x :=
  (equiv B hc hB).symm_apply_apply x

theorem norm_inverse_apply (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) (x : H) : ‖inverse B hc hB x‖ ≤ c⁻¹ * ‖x‖ := by
  let y := inverse B hc hB x
  have hBy : B y = x := apply_inverse B hc hB x
  have hh := hB y
  rw [hBy] at hh
  have hi := re_inner_le_norm (𝕜 := ℂ) y x
  change (inner ℂ y x).re ≤ ‖y‖ * ‖x‖ at hi
  by_cases hy : y = 0
  · change ‖y‖ ≤ _
    rw [hy, norm_zero]
    positivity
  · have hypos := norm_pos_iff.mpr hy
    have hmul : c * ‖y‖ ≤ ‖x‖ := by nlinarith
    change ‖y‖ ≤ c⁻¹ * ‖x‖
    rw [inv_mul_eq_div, le_div_iff₀ hc]
    linarith

theorem norm_inverse (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) : ‖inverse B hc hB‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    (norm_inverse_apply B hc hB)

theorem inverse_symmetric (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) (hs : B.IsSymmetric) : (inverse B hc hB).IsSymmetric := by
  intro x y
  have h := hs (inverse B hc hB x) (inverse B hc hB y)
  simpa only [ContinuousLinearMap.coe_coe, apply_inverse] using h.symm

theorem inverse_nonnegative (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) (x : H) : 0 ≤ (inner ℂ x (inverse B hc hB x)).re := by
  have h := hB (inverse B hc hB x)
  rw [apply_inverse] at h
  have hr : (inner ℂ (inverse B hc hB x) x).re =
      (inner ℂ x (inverse B hc hB x)).re := inner_re_symm (𝕜 := ℂ) _ _
  rw [hr] at h
  exact (mul_nonneg hc.le (sq_nonneg _)).trans h

/-- Completing the square gives the variational upper bound for the inverse. -/
theorem inverse_variational (B : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hB : Coercive B c) (hs : B.IsSymmetric) (x y : H) :
    2 * (inner ℂ x y).re - (inner ℂ y (B y)).re ≤
      (inner ℂ x (inverse B hc hB x)).re := by
  let z := inverse B hc hB x
  have hBz : B z = x := apply_inverse B hc hB x
  have hn : 0 ≤ (inner ℂ (y - z) (B (y - z))).re :=
    (mul_nonneg hc.le (sq_nonneg _)).trans (hB _)
  have hzy : (inner ℂ z (B y)).re = (inner ℂ x y).re := by
    have h := hs z y
    change inner ℂ (B z) y = inner ℂ z (B y) at h
    rw [hBz] at h
    exact congrArg Complex.re h.symm
  have hyx : (inner ℂ y x).re = (inner ℂ x y).re := inner_re_symm (𝕜 := ℂ) y x
  have hzx : (inner ℂ z x).re = (inner ℂ x z).re := inner_re_symm (𝕜 := ℂ) z x
  simp only [map_sub, hBz, inner_sub_left, inner_sub_right, Complex.sub_re,
    hzy, hyx, hzx] at hn
  change 2 * (inner ℂ x y).re - (inner ℂ y (B y)).re ≤ (inner ℂ x z).re
  linarith

/-- Order reversal follows from positivity, with no diagonalization hypothesis. -/
theorem inverse_antitone (B D : H →L[ℂ] H) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hB : Coercive B c) (hD : Coercive D d) (hs : B.IsSymmetric)
    (hle : ∀ y, (inner ℂ y (B y)).re ≤ (inner ℂ y (D y)).re) (x : H) :
    (inner ℂ x (inverse D hd hD x)).re ≤ (inner ℂ x (inverse B hc hB x)).re := by
  let y := inverse D hd hD x
  have hDy : D y = x := apply_inverse D hd hD x
  have hq := hle y
  have hyx : (inner ℂ y x).re = (inner ℂ x y).re := inner_re_symm (𝕜 := ℂ) y x
  rw [hDy, hyx] at hq
  have hv := inverse_variational B hc hB hs x y
  change (inner ℂ x y).re ≤ _
  linarith

end Maxwell.Continuum.CoerciveInverse
