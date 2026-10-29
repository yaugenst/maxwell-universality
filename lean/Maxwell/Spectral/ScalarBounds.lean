import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Exact scalar estimates in the local spectral-polynomial argument

These real inequalities formalize the scalar calculation in
`results/main/verify_local_edge_scalar.py`. The finite-matrix premises,
Taylor coefficient norm estimates and the min-max
argument are separate obligations; this file does not assume their conclusion.
-/

namespace Maxwell.Spectral

noncomputable section

/-- The exact scalar coefficient multiplying the quadratic form in the paper.
The square-root quotient in the manuscript simplifies to `sqrt 180`. -/
def localPolynomialMargin (r δ E : ℝ) : ℝ :=
  (7 / 256 - E) - 100 * δ - (18 / 5) * r ^ 2 -
    (7 / 256 - E) * 130 * r ^ 2 - 8 * δ * r ^ 2 -
    ((4 / 25) * Real.sqrt 180 + 289 / 8) * r ^ 4 - (8 / 25) * r ^ 6

theorem sqrt_180_lt : Real.sqrt (180 : ℝ) < 27 / 2 := by
  apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
  norm_num

/-- The simplified radical is exactly the quotient in the manuscript. -/
theorem sqrt_ratio_eq :
    Real.sqrt (18 / 5 : ℝ) / Real.sqrt (1 / 50 : ℝ) = Real.sqrt 180 := by
  rw [← Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 18 / 5)]
  norm_num

/-- Algebraic correspondence with the unsimplified constants of the proof. -/
theorem localPolynomialMargin_eq_original (r δ E : ℝ) :
    localPolynomialMargin r δ E =
      (7 / 256 - E) - 2 * δ * 1 / (1 / 50) - (18 / 5) * r ^ 2 -
      (7 / 256 - E) * ((13 / 5) / (1 / 50)) * r ^ 2 -
      (2 * δ * (2 / 25) / (1 / 50)) * r ^ 2 -
      (2 * Real.sqrt (18 / 5) * (2 / 25) / Real.sqrt (1 / 50) +
        (17 / 20) ^ 2 / (1 / 50)) * r ^ 4 -
      ((2 / 25) ^ 2 / (1 / 50)) * r ^ 6 := by
  have hrad : 2 * Real.sqrt (18 / 5 : ℝ) * (2 / 25) / Real.sqrt (1 / 50) =
      (4 / 25) * Real.sqrt 180 := by
    calc
      _ = (4 / 25) * (Real.sqrt (18 / 5 : ℝ) / Real.sqrt (1 / 50)) := by ring
      _ = _ := by rw [sqrt_ratio_eq]
  rw [hrad]
  unfold localPolynomialMargin
  ring

/-- Radius powers used to make each nonnegative loss uniform on the ball. -/
theorem radius_power_bounds (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) :
    r ^ 2 ≤ 1 / 400 ∧ r ^ 4 ≤ 1 / 160000 ∧ r ^ 6 ≤ 1 / 64000000 := by
  have h2 := pow_le_pow_left₀ hr0 hr 2
  have h4 := pow_le_pow_left₀ hr0 hr 4
  have h6 := pow_le_pow_left₀ hr0 hr 6
  norm_num at h2 h4 h6
  exact ⟨h2, h4, h6⟩

/-- A rational lower bound, with the positive and negative occurrences of
`7/256 - E` bounded in their respective directions. -/
theorem localPolynomialMargin_lower (r δ E : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (_hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000) :
    (2178546479 : ℝ) / 819200000000 ≤ localPolynomialMargin r δ E := by
  obtain ⟨hr2, hr4, hr6⟩ := radius_power_bounds r hr0 hr
  have hδr2 : δ * r ^ 2 ≤ (1 / (2 : ℝ) ^ 20) * (1 / 400) :=
    mul_le_mul hδ hr2 (sq_nonneg r) (by norm_num)
  have hBr2 : (7 / 256 - E) * r ^ 2 ≤
      (7 / 256 - 239 / 25000 : ℝ) * (1 / 400) :=
    mul_le_mul (by linarith) hr2 (sq_nonneg r) (by norm_num)
  have hrad : (4 / 25 : ℝ) * Real.sqrt 180 + 289 / 8 ≤
      (4 / 25) * (27 / 2) + 289 / 8 := by
    have := sqrt_180_lt
    linarith
  have hradr4 : ((4 / 25 : ℝ) * Real.sqrt 180 + 289 / 8) * r ^ 4 ≤
      ((4 / 25) * (27 / 2) + 289 / 8) * (1 / 160000) :=
    mul_le_mul hrad hr4 (pow_nonneg hr0 4) (by norm_num)
  unfold localPolynomialMargin
  norm_num at hδ hδr2 hBr2 hradr4
  nlinarith only [hδ, hEhi, hr2, hr6, hδr2, hBr2, hradr4]

/-- The local polynomial margin is positive uniformly, including at radius
zero. This is a scalar implication, not a spectral-isolation theorem. -/
theorem localPolynomialMargin_gt (r δ E : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hElo : 239 / 25000 ≤ E) (hEhi : E ≤ 957 / 100000) :
    1 / 400 < localPolynomialMargin r δ E := by
  have h := localPolynomialMargin_lower r δ E hr0 hr hδ0 hδ hElo hEhi
  linarith

/-- The constant scalar term retained before estimating the radius losses. -/
theorem constant_term_nonnegative (δ E : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (2 : ℝ) ^ 20)
    (hEhi : E ≤ 957 / 100000) :
    0 ≤ δ * ((7 / 256 - E) - δ) := by
  apply mul_nonneg hδ0
  norm_num at hδ
  linarith

/-- The exact rational coercivity obtained after trial-space normalization. -/
theorem band_coercivity_lower :
    ((1 / 400 : ℝ) * (1 / 50) / (1 + 9 * (1 / 20) ^ 2) / (7 / 256)) =
      128 / 71575 := by norm_num

theorem band_coercivity_gt : (1 / 600 : ℝ) < 128 / 71575 := by norm_num

/-- Uniform version of the same normalization arithmetic. -/
theorem band_coercivity_radius_gt (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) :
    (1 / 600 : ℝ) < 1 / (20000 * (1 + 9 * r ^ 2) * (7 / 256)) := by
  have hr2 := (radius_power_bounds r hr0 hr).1
  have hden : (0 : ℝ) < 20000 * (1 + 9 * r ^ 2) * (7 / 256) := by positivity
  apply (lt_div_iff₀ hden).2
  nlinarith only [hr2]

/-- Rational majorant for a positive-degree curl-square coefficient. -/
def taylorCoefficientMajorant (j : ℕ) : ℝ :=
  (4 * (2 : ℝ) ^ j + 6) * (11 / 70) ^ j / (Nat.factorial j : ℝ)

theorem tail_ratio_lt :
    (((2 : ℝ) * (11 / 70) * (1 / 20)) ^ 2 / 12) < 1 / 40000 := by norm_num

/-- These three checks certify the leading coefficients times the proposed
geometric multiplier. The analytic tail-ratio premise is proved separately. -/
theorem taylor_majorant_coefficients :
    (taylorCoefficientMajorant 4 + 6 * taylorCoefficientMajorant 3 +
        9 * taylorCoefficientMajorant 2) / (1 - (1 / 40000 : ℝ)) < 13 / 5 ∧
    (taylorCoefficientMajorant 3 + 3 * taylorCoefficientMajorant 2) /
        (1 - (1 / 40000 : ℝ)) < 17 / 20 ∧
    (taylorCoefficientMajorant 4 + 3 * taylorCoefficientMajorant 3) /
        (1 - (1 / 40000 : ℝ)) < 2 / 25 := by
  norm_num [taylorCoefficientMajorant, Nat.factorial]

theorem taylorCoefficientMajorant_nonnegative (j : ℕ) :
    0 ≤ taylorCoefficientMajorant j := by
  unfold taylorCoefficientMajorant
  positivity

/-- The two-degree coefficient recurrence, with the smallest denominator
`(j+1)(j+2) ≥ 12` taken only for `j ≥ 2`. -/
theorem taylorCoefficientMajorant_step (j : ℕ) (hj : 2 ≤ j) :
    taylorCoefficientMajorant (j + 2) ≤
      (4 * (11 / 70 : ℝ) ^ 2 / 12) * taylorCoefficientMajorant j := by
  have hj' : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hfact : ((j + 2).factorial : ℝ) =
      ((j : ℝ) + 2) * ((j : ℝ) + 1) * (j.factorial : ℝ) := by
    simp [Nat.factorial_succ]
    ring
  have hden : 12 * (j.factorial : ℝ) ≤ ((j + 2).factorial : ℝ) := by
    rw [hfact]
    have hprod : (12 : ℝ) ≤ ((j : ℝ) + 2) * ((j : ℝ) + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_right hprod (by positivity)
  have hnum : (4 * (2 : ℝ) ^ (j + 2) + 6) * (11 / 70) ^ (j + 2) ≤
      4 * (4 * (2 : ℝ) ^ j + 6) * (11 / 70) ^ j * (11 / 70) ^ 2 := by
    rw [pow_add, pow_add]
    have hnonneg : 0 ≤ (11 / 70 : ℝ) ^ j := by positivity
    nlinarith only [hnonneg]
  unfold taylorCoefficientMajorant
  calc
    _ ≤ (4 * (4 * (2 : ℝ) ^ j + 6) * (11 / 70) ^ j * (11 / 70) ^ 2) /
        (12 * (j.factorial : ℝ)) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = _ := by ring

/-- Every relevant even-step Taylor loss contracts by at least the fixed
geometric factor throughout the radius-`1/20` ball. -/
theorem taylorCoefficientMajorant_radius_step (j : ℕ) (hj : 2 ≤ j)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) :
    taylorCoefficientMajorant (j + 2) * r ^ 2 ≤
      taylorCoefficientMajorant j / 40000 := by
  have hstep := taylorCoefficientMajorant_step j hj
  have hr2 := (radius_power_bounds r hr0 hr).1
  have ha := taylorCoefficientMajorant_nonnegative j
  have hprod := mul_le_mul hstep hr2 (sq_nonneg r)
    (by positivity : 0 ≤ (4 * (11 / 70 : ℝ) ^ 2 / 12) * taylorCoefficientMajorant j)
  nlinarith only [hprod, ha]

/-- A genuine infinite-series comparison, rather than a finite truncation. -/
theorem geometric_majorant (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hstep : ∀ n, f (n + 1) ≤ f n / 40000) :
    Summable f ∧ (∑' n, f n) ≤ f 0 / (1 - (1 / 40000 : ℝ)) := by
  have hbound : ∀ n, f n ≤ f 0 * (1 / 40000 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        f (n + 1) ≤ f n * (1 / 40000) := by simpa [div_eq_mul_inv] using hstep n
        _ ≤ (f 0 * (1 / 40000 : ℝ) ^ n) * (1 / 40000) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = f 0 * (1 / 40000 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  have hgeom := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 40000) (by norm_num : (1 / 40000 : ℝ) < 1)).mul_left (f 0)
  have hs : Summable f := Summable.of_nonneg_of_le hf0 hbound hgeom.summable
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_tsum hbound hgeom.summable
  rw [hgeom.tsum_eq] at ht
  simpa [div_eq_mul_inv] using ht

/-- A Taylor tail may have a fixed radius power different from its initial
coefficient degree, as occurs after multiplying by the linear corrector. -/
def taylorTail (j d : ℕ) (r : ℝ) (n : ℕ) : ℝ :=
  taylorCoefficientMajorant (j + 2 * n) * r ^ (d + 2 * n)

theorem taylorTail_nonnegative (j d : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (n : ℕ) :
    0 ≤ taylorTail j d r n :=
  mul_nonneg (taylorCoefficientMajorant_nonnegative _) (pow_nonneg hr0 _)

theorem taylorTail_step (j d : ℕ) (hj : 2 ≤ j)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) (n : ℕ) :
    taylorTail j d r (n + 1) ≤ taylorTail j d r n / 40000 := by
  have h := taylorCoefficientMajorant_radius_step (j + 2 * n) (by omega) r hr0 hr
  have hm := mul_le_mul_of_nonneg_right h (pow_nonneg hr0 (d + 2 * n))
  have hjn : j + 2 * (n + 1) = (j + 2 * n) + 2 := by omega
  have hdn : d + 2 * (n + 1) = (d + 2 * n) + 2 := by omega
  unfold taylorTail
  rw [hjn, hdn, pow_add]
  nlinarith only [hm]

theorem taylorTail_bound (j d : ℕ) (hj : 2 ≤ j)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) :
    Summable (taylorTail j d r) ∧ (∑' n, taylorTail j d r n) ≤
      taylorCoefficientMajorant j * r ^ d / (1 - (1 / 40000 : ℝ)) := by
  simpa [taylorTail] using geometric_majorant (taylorTail j d r)
    (taylorTail_nonnegative j d r hr0) (taylorTail_step j d hj r hr0 hr)

def kRemainderMajorant (r : ℝ) (n : ℕ) : ℝ :=
  taylorTail 4 4 r n + 6 * taylorTail 3 4 r n + 9 * taylorTail 2 4 r n

def evenResidualMajorant (r : ℝ) (n : ℕ) : ℝ :=
  taylorTail 4 4 r n + 3 * taylorTail 3 4 r n

def oddResidualMajorant (r : ℝ) (n : ℕ) : ℝ :=
  taylorTail 3 3 r n + 3 * taylorTail 2 3 r n

/-- Exact infinite tail bound corresponding to `‖K_rem‖ ≤ (13/5) r⁴`.
Relating the operator's norm to this series remains an operator theorem. -/
theorem kRemainderMajorant_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) :
    Summable (kRemainderMajorant r) ∧
      (∑' n, kRemainderMajorant r n) ≤ (13 / 5) * r ^ 4 := by
  have hf0 : ∀ n, 0 ≤ kRemainderMajorant r n := by
    intro n
    have h4 := taylorTail_nonnegative 4 4 r hr0 n
    have h3 := taylorTail_nonnegative 3 4 r hr0 n
    have h2 := taylorTail_nonnegative 2 4 r hr0 n
    unfold kRemainderMajorant
    linarith
  have hstep : ∀ n, kRemainderMajorant r (n + 1) ≤ kRemainderMajorant r n / 40000 := by
    intro n
    have h4 := taylorTail_step 4 4 (by norm_num) r hr0 hr n
    have h3 := taylorTail_step 3 4 (by norm_num) r hr0 hr n
    have h2 := taylorTail_step 2 4 (by norm_num) r hr0 hr n
    unfold kRemainderMajorant
    linarith
  obtain ⟨hs, ht⟩ := geometric_majorant (kRemainderMajorant r) hf0 hstep
  refine ⟨hs, ht.trans ?_⟩
  norm_num [kRemainderMajorant, taylorTail, taylorCoefficientMajorant, Nat.factorial]
  nlinarith only [pow_nonneg hr0 4]

/-- Exact infinite even-residual tail bound, including radius zero. -/
theorem evenResidualMajorant_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) :
    Summable (evenResidualMajorant r) ∧
      (∑' n, evenResidualMajorant r n) ≤ (2 / 25) * r ^ 4 := by
  have hf0 : ∀ n, 0 ≤ evenResidualMajorant r n := by
    intro n
    have h4 := taylorTail_nonnegative 4 4 r hr0 n
    have h3 := taylorTail_nonnegative 3 4 r hr0 n
    unfold evenResidualMajorant
    linarith
  have hstep : ∀ n, evenResidualMajorant r (n + 1) ≤ evenResidualMajorant r n / 40000 := by
    intro n
    have h4 := taylorTail_step 4 4 (by norm_num) r hr0 hr n
    have h3 := taylorTail_step 3 4 (by norm_num) r hr0 hr n
    unfold evenResidualMajorant
    linarith
  obtain ⟨hs, ht⟩ := geometric_majorant (evenResidualMajorant r) hf0 hstep
  refine ⟨hs, ht.trans ?_⟩
  norm_num [evenResidualMajorant, taylorTail, taylorCoefficientMajorant, Nat.factorial]
  nlinarith only [pow_nonneg hr0 4]

/-- Exact infinite odd-residual tail bound, including radius zero. -/
theorem oddResidualMajorant_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 20) :
    Summable (oddResidualMajorant r) ∧
      (∑' n, oddResidualMajorant r n) ≤ (17 / 20) * r ^ 3 := by
  have hf0 : ∀ n, 0 ≤ oddResidualMajorant r n := by
    intro n
    have h3 := taylorTail_nonnegative 3 3 r hr0 n
    have h2 := taylorTail_nonnegative 2 3 r hr0 n
    unfold oddResidualMajorant
    linarith
  have hstep : ∀ n, oddResidualMajorant r (n + 1) ≤ oddResidualMajorant r n / 40000 := by
    intro n
    have h3 := taylorTail_step 3 3 (by norm_num) r hr0 hr n
    have h2 := taylorTail_step 2 3 (by norm_num) r hr0 hr n
    unfold oddResidualMajorant
    linarith
  obtain ⟨hs, ht⟩ := geometric_majorant (oddResidualMajorant r) hf0 hstep
  refine ⟨hs, ht.trans ?_⟩
  norm_num [oddResidualMajorant, taylorTail, taylorCoefficientMajorant, Nat.factorial]
  nlinarith only [pow_nonneg hr0 3]

end

end Maxwell.Spectral
