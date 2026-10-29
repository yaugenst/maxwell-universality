import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exponential-rate selection and removal of the algebraic Green prefactors. -/

namespace Maxwell.Green

open Filter
open scoped Topology

/-- The placement distortion used in the paper leaves a strict decay margin. -/
theorem placement_rate_margin :
    (1 + (1 : ℝ) / 100) ^ 2 < 2 * (1 - (1 : ℝ) / 100) ^ 2 / Real.sqrt 3 := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply (lt_div_iff₀ hs).2
  nlinarith [sq_nonneg (Real.sqrt (3 : ℝ) - 19 / 10)]

/-- A common positive scale preserves the strict margin between axial and
twice the global decay exponent. -/
theorem scaled_placement_rate_margin (s : ℝ) (hs : 0 < s) :
    (1 + (1 : ℝ) / 100) ^ 2 * s <
      2 * (((1 - (1 : ℝ) / 100) ^ 2 / Real.sqrt 3) * s) := by
  have h := mul_lt_mul_of_pos_right placement_rate_margin hs
  convert h using 1
  ring

/-- Strict real decay margins admit rational rates with the required square
separation. All rate inequalities are in the real embedding of the rationals. -/
theorem exists_rational_rates (U V : ℝ) (hV : 0 < V) (hVU : V < 2 * U) :
    ∃ r a : ℚ, 0 < (r : ℝ) ∧ (r : ℝ) < 1 ∧
      0 < (a : ℝ) ∧ (a : ℝ) < 1 ∧
      Real.exp (-U) < (r : ℝ) ∧ (r : ℝ) ^ 2 < (a : ℝ) ∧
      (a : ℝ) < Real.exp (-V) := by
  have hm : Real.exp (-U) < Real.exp (-V / 2) := by
    apply Real.exp_lt_exp.mpr
    linarith
  obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn hm
  have hr₀ : 0 < (r : ℝ) := (Real.exp_pos _).trans hr₁
  have hrsq : (r : ℝ) ^ 2 < Real.exp (-V) := by
    calc
      (r : ℝ) ^ 2 < Real.exp (-V / 2) ^ 2 := by nlinarith [Real.exp_pos (-V / 2)]
      _ = Real.exp (-V) := by rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
  obtain ⟨a, ha₁, ha₂⟩ := exists_rat_btwn hrsq
  have ha₀ : 0 < (a : ℝ) := (sq_pos_of_pos hr₀).trans ha₁
  have he : Real.exp (-V) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hr₃ : (r : ℝ) < 1 := by
    have he' : Real.exp (-V / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact hr₂.trans he'
  exact ⟨r, a, hr₀, hr₃, ha₀, ha₂.trans he, hr₁, ha₁, ha₂⟩

/-- Any fixed positive leading coefficient and any polynomial prefactor are
absorbed by a strict exponential margin. -/
theorem eventually_exp_le_polynomial_exp (c p I J : ℝ)
    (hc : 0 < c) (hIJ : I < J) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-J * x) ≤ c / x ^ p * Real.exp (-I * x) := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (J - I)
    (sub_pos.mpr hIJ)
  have he : ∀ᶠ x : ℝ in atTop, x ^ p * Real.exp (-(J - I) * x) < c :=
    ht.eventually (gt_mem_nhds hc)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x hx hx₀
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx₀ p
  have hex : Real.exp (-J * x) =
      Real.exp (-(J - I) * x) * Real.exp (-I * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hex]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  exact (le_div_iff₀ hxp).2 (by nlinarith)

/-- A higher inverse power is eventually smaller than any prescribed positive
multiple of a lower inverse power. -/
theorem eventually_polynomial_remainder_small (c K p q : ℝ)
    (hc : 0 < c) (hpq : p < q) :
    ∀ᶠ x : ℝ in atTop, |K| / x ^ q ≤ c / x ^ p := by
  have ht : Tendsto (fun x : ℝ => |K| * x ^ (p - q)) atTop (𝓝 0) := by
    have ht' := (tendsto_rpow_neg_atTop (sub_pos.mpr hpq)).const_mul |K|
    simpa only [neg_sub, mul_zero] using ht'
  have he := ht.eventually (gt_mem_nhds hc)
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x hx hx₀
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx₀ p
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx₀ q
  rw [Real.rpow_sub hx₀] at hx
  apply (div_le_div_iff₀ hxq hxp).2
  have hmul : |K| * x ^ p < c * x ^ q :=
    (div_lt_iff₀ hxq).1 (by simpa only [mul_div_assoc] using hx)
  exact hmul.le

/-- The effective Green asymptotic's `d⁻³ᐟ²` remainder is absorbed by half
of its positive `d⁻¹` leading term. The strict exponential margin then
absorbs that remaining `d⁻¹` factor. -/
theorem eventually_green_lower_bound (c K I J : ℝ) (hc : 0 < c) (hIJ : I < J)
    (R : ℝ → ℝ) (hR : ∀ᶠ x : ℝ in atTop,
      |R x| ≤ |K| / x ^ ((3 : ℝ) / 2)) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-J * x) ≤ |Real.exp (-I * x) * (c / x + R x)| := by
  have herr := eventually_polynomial_remainder_small (c / 2) K 1 (3 / 2)
    (by linarith) (by norm_num)
  have hmain := eventually_exp_le_polynomial_exp (c / 2) 1 I J (by linarith) hIJ
  filter_upwards [herr, hmain, hR, eventually_gt_atTop (0 : ℝ)] with x he hm hr hx
  simp only [Real.rpow_one] at he hm
  have hr' : |R x| ≤ (c / 2) / x := hr.trans he
  have hcoeff : (c / 2) / x ≤ |c / x + R x| := by
    have hneg := neg_abs_le (R x)
    have habs := le_abs_self (c / x + R x)
    have hsplit : c / x = 2 * ((c / 2) / x) := by ring
    linarith
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-J * x) ≤ (c / 2) / x * Real.exp (-I * x) := hm
    _ ≤ |c / x + R x| * Real.exp (-I * x) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
    _ = Real.exp (-I * x) * |c / x + R x| := by ring

/-- Integer-distance version of exponential absorption, directly giving a
geometric lower rate from the strict margin `a < exp (-I)`. -/
theorem eventually_nat_geometric_lower (a c p I : ℝ) (ha : 0 < a)
    (hc : 0 < c) (haI : a < Real.exp (-I)) :
    ∀ᶠ n : ℕ in atTop,
      a ^ n ≤ c / (n : ℝ) ^ p * Real.exp (-I * (n : ℝ)) := by
  have hIJ : I < -Real.log a := by
    have hlog := Real.log_lt_log ha haI
    rw [Real.log_exp] at hlog
    linarith
  have he := (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from
    tendsto_natCast_atTop_atTop).eventually
      (eventually_exp_le_polynomial_exp c p I (-Real.log a) hc hIJ)
  change ∀ᶠ n : ℕ in atTop,
    Real.exp (- -Real.log a * (n : ℝ)) ≤
      c / (n : ℝ) ^ p * Real.exp (-I * (n : ℝ)) at he
  simpa only [neg_neg, Real.exp_mul, Real.exp_log ha, Real.rpow_natCast] using he

/-- An exponential upper estimate is also an upper estimate at every larger
geometric rate, with no large-distance restriction. -/
theorem exp_decay_le_geometric (U r : ℝ) (hr : Real.exp (-U) ≤ r) (n : ℕ) :
    Real.exp (-U * (n : ℝ)) ≤ r ^ n := by
  rw [Real.exp_mul, Real.rpow_natCast]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hr n

/-- The Green remainder need only be known at integer lattice distances.
This closes both prefactor absorptions directly on that domain. -/
theorem eventually_nat_green_geometric_lower (a c K I : ℝ)
    (ha : 0 < a) (hc : 0 < c) (haI : a < Real.exp (-I))
    (R : ℕ → ℝ) (hR : ∀ᶠ n : ℕ in atTop,
      |R n| ≤ |K| / (n : ℝ) ^ ((3 : ℝ) / 2)) :
    ∀ᶠ n : ℕ in atTop,
      a ^ n ≤ |Real.exp (-I * (n : ℝ)) * (c / (n : ℝ) + R n)| := by
  have herr := (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from
    tendsto_natCast_atTop_atTop).eventually
      (eventually_polynomial_remainder_small (c / 2) K 1 (3 / 2)
        (by linarith) (by norm_num))
  have hmain := eventually_nat_geometric_lower a (c / 2) 1 I ha (by linarith) haI
  filter_upwards [herr, hmain, hR] with n he hm hr
  simp only [Real.rpow_one] at he hm
  have hr' : |R n| ≤ (c / 2) / (n : ℝ) := hr.trans he
  have hcoeff : (c / 2) / (n : ℝ) ≤ |c / (n : ℝ) + R n| := by
    have hneg := neg_abs_le (R n)
    have habs := le_abs_self (c / (n : ℝ) + R n)
    have hsplit : c / (n : ℝ) = 2 * ((c / 2) / (n : ℝ)) := by ring
    linarith
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    a ^ n ≤ (c / 2) / (n : ℝ) * Real.exp (-I * (n : ℝ)) := hm
    _ ≤ |c / (n : ℝ) + R n| * Real.exp (-I * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
    _ = Real.exp (-I * (n : ℝ)) * |c / (n : ℝ) + R n| := by ring

/-- The upper axial exponent bound transfers the common rational lower rate
to each individual axial exponent. -/
theorem lower_rate_of_exponent_le (a I V : ℝ)
    (haV : a < Real.exp (-V)) (hIV : I ≤ V) : a < Real.exp (-I) :=
  haV.trans_le (Real.exp_le_exp.mpr (neg_le_neg hIV))

/-- Finitely many axial asymptotics admit a single integer distance threshold.
In the physical placement this is applied to the three coordinate axes. -/
theorem exists_common_green_threshold {ι : Type*} [Finite ι]
    (a V : ℝ) (c K I : ι → ℝ) (R : ι → ℕ → ℝ)
    (ha : 0 < a) (haV : a < Real.exp (-V))
    (hc : ∀ j, 0 < c j) (hIV : ∀ j, I j ≤ V)
    (hR : ∀ j, ∀ᶠ n : ℕ in atTop,
      |R j n| ≤ |K j| / (n : ℝ) ^ ((3 : ℝ) / 2)) :
    ∃ d₀ : ℕ, ∀ n ≥ d₀, ∀ j,
      a ^ n ≤ |Real.exp (-I j * (n : ℝ)) * (c j / (n : ℝ) + R j n)| := by
  have he : ∀ j, ∀ᶠ n : ℕ in atTop,
      a ^ n ≤ |Real.exp (-I j * (n : ℝ)) * (c j / (n : ℝ) + R j n)| := by
    intro j
    exact eventually_nat_green_geometric_lower a (c j) (K j) (I j) ha (hc j)
      (lower_rate_of_exponent_le a (I j) V haV (hIV j)) (R j) (hR j)
  exact Filter.eventually_atTop.1 (Filter.eventually_all.2 he)

end Maxwell.Green
