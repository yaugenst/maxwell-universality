import Maxwell.Spectral.ScalarBounds
import Maxwell.Spectral.Neighborhood
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module

/-!
# The full residual-square coercivity estimate

This module retains the complete residual, including the cluster offset and
both parity remainders. A rational upper bound for the quadratic residual
replaces the square root in the manuscript; its smaller positive margin still
proves exactly the required `1/20000` coercivity.
-/

namespace Maxwell.Spectral

noncomputable section

def rationalPolynomialMargin (r δ E : ℝ) : ℝ :=
  (7 / 256 - E) - 100 * δ - (18 / 5) * r ^ 2 -
    (7 / 256 - E) * 130 * r ^ 2 - 8 * δ * r ^ 2 -
    (417 / 8) * r ^ 4 - (8 / 25) * r ^ 6

theorem rationalPolynomialMargin_gt (r δ E : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000) :
    1 / 400 < rationalPolynomialMargin r δ E := by
  obtain ⟨hr2, hr4, hr6⟩ := radius_power_bounds r hr0 hr
  have hδr2 : δ * r ^ 2 ≤ (1 / (2 : ℝ) ^ 20) * (1 / 400) :=
    mul_le_mul hδ hr2 (sq_nonneg r) (by norm_num)
  have hBr2 : (7 / 256 - E) * r ^ 2 ≤
      (7 / 256 - 239 / 25000 : ℝ) * (1 / 400) :=
    mul_le_mul (by linarith) hr2 (sq_nonneg r) (by norm_num)
  have hlower : (2107685679 : ℝ) / 819200000000 ≤
      rationalPolynomialMargin r δ E := by
    unfold rationalPolynomialMargin
    norm_num at hδ hδr2 hBr2
    nlinarith only [hδ, hEhi, hr2, hr4, hr6, hδr2, hBr2]
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem edgePolynomialMap_quadratic (A : H →ₗ[ℂ] H) (hA : A.IsSymmetric)
    (E b : ℝ) (v : H) :
    Complex.re (inner ℂ v (edgePolynomialMap A E b v)) =
      (b - E) * Complex.re (inner ℂ v ((A - (E : ℂ) •
        (LinearMap.id : H →ₗ[ℂ] H)) v)) -
        ‖(A - (E : ℂ) • (LinearMap.id : H →ₗ[ℂ] H)) v‖ ^ 2 := by
  let X := A - (E : ℂ) • (LinearMap.id : H →ₗ[ℂ] H)
  have hX : X.IsSymmetric := hA.sub (LinearMap.IsSymmetric.id.smul (by simp))
  have hid : edgePolynomialMap A E b v = ((b - E : ℝ) : ℂ) • X v - X (X v) := by
    simp only [edgePolynomialMap, X, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, Complex.ofReal_sub]
    module
  rw [hid, inner_sub_right, inner_smul_right, ← hX v (X v)]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hn := norm_sq_eq_re_inner (𝕜 := ℂ) (X v)
  change ‖X v‖ ^ 2 = Complex.re (inner ℂ (X v) (X v)) at hn
  rw [← hn]


theorem norm_three_add_sq_le (a b c : H) :
    ‖a + b + c‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 +
      2 * Complex.re (inner ℂ a b) +
      2 * ‖a‖ * ‖c‖ + 2 * ‖b‖ * ‖c‖ := by
  rw [norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), inner_add_left, map_add]
  have ha := re_inner_le_norm (𝕜 := ℂ) a c
  have hb := re_inner_le_norm (𝕜 := ℂ) b c
  simp only [RCLike.re_to_complex] at ha hb ⊢
  nlinarith only [ha, hb]

/-- Pointwise quadratic estimate for the actual full residual.

`t` is the cluster-offset quadratic form, `k` the second-order compressed
form, `a` the offset residual, `b` the second-order residual, and `c,d` the
even/odd remainder vectors. The special cross term is preserved instead of
being replaced by a wasteful product of norms. -/
theorem full_residual_coercivity (r δ E n t k f : ℝ) (a b c d : H)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000)
    (hn : 0 ≤ n)
    (hklo : r ^ 2 * n ^ 2 / 50 ≤ k) (hkhi : k ≤ r ^ 2 * n ^ 2)
    (ha : ‖a‖ ≤ δ * n)
    (hb : ‖b‖ ^ 2 ≤ (18 / 5) * r ^ 2 * k)
    (hc : ‖c‖ ≤ (2 / 25) * r ^ 4 * n)
    (hd : ‖d‖ ≤ (17 / 20) * r ^ 3 * n)
    (hab : Complex.re (inner ℂ a b) ≤ δ * r ^ 2 * n ^ 2)
    (hcenter : ‖a‖ ^ 2 ≤ (7 / 256 - E) * t)
    (hf : t + k - (13 / 5) * r ^ 4 * n ^ 2 ≤ f) :
    r ^ 2 * n ^ 2 / 20000 ≤
      (7 / 256 - E) * f - ‖a + b + c‖ ^ 2 - ‖d‖ ^ 2 := by
  have hB : 0 ≤ 7 / 256 - E := by linarith
  have hk : 0 ≤ k := le_trans (by positivity) hklo
  have hb' : ‖b‖ ≤ 2 * r ^ 2 * n := by
    have h := mul_le_mul_of_nonneg_left hkhi
      (show 0 ≤ (18 / 5 : ℝ) * r ^ 2 by positivity)
    have hn' : 0 ≤ 2 * r ^ 2 * n := by positivity
    nlinarith only [hb, h, norm_nonneg b, hn', sq_nonneg (r ^ 2 * n)]
  have hac := mul_le_mul ha hc (norm_nonneg c) (mul_nonneg hδ0 hn)
  have hbc := mul_le_mul hb' hc (norm_nonneg c) (by positivity : 0 ≤ 2 * r ^ 2 * n)
  have hc2 := pow_le_pow_left₀ (norm_nonneg c) hc 2
  have hd2 := pow_le_pow_left₀ (norm_nonneg d) hd 2
  have hnorm := norm_three_add_sq_le a b c
  have hfB := mul_le_mul_of_nonneg_left hf hB
  have h100 := mul_le_mul_of_nonneg_left hklo (by positivity : 0 ≤ 100 * δ)
  have h130 := mul_le_mul_of_nonneg_left hklo
    (by positivity : 0 ≤ 130 * (7 / 256 - E) * r ^ 2)
  have h8 := mul_le_mul_of_nonneg_left hklo (by positivity : 0 ≤ 8 * δ * r ^ 2)
  have h16 := mul_le_mul_of_nonneg_left hklo (by positivity : 0 ≤ 16 * r ^ 4)
  have h289 := mul_le_mul_of_nonneg_left hklo (by positivity : 0 ≤ (289 / 8 : ℝ) * r ^ 4)
  have hsmall := mul_le_mul_of_nonneg_left hklo (by positivity : 0 ≤ (8 / 25 : ℝ) * r ^ 6)
  have hpoly : rationalPolynomialMargin r δ E * k ≤
      (7 / 256 - E) * f - ‖a + b + c‖ ^ 2 - ‖d‖ ^ 2 := by
    unfold rationalPolynomialMargin
    nlinarith only [hab, hb, hac, hbc, hc2, hd2, hnorm, hfB, hcenter,
      h100, h130, h8, h16, h289, hsmall]
  have hmargin := le_of_lt (rationalPolynomialMargin_gt r δ E hr0 hr hδ hElo hEhi)
  have hmul := mul_le_mul_of_nonneg_right hmargin hk
  nlinarith only [hpoly, hmul, hklo]

end
end Maxwell.Spectral
