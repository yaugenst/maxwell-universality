import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Effective integer spacing from the strict separation of the fixed
geometric rates. The natural search tests rational inequalities; its
termination and logarithmic upper bound are proved using real logarithms. -/
namespace Maxwell.Realization

/-- A logarithmic witness for a contractive geometric sequence. -/
noncomputable def geometricCeiling (ρ target : ℝ) : ℕ :=
  ⌈Real.log target / Real.log ρ⌉₊

theorem pow_geometricCeiling_le (ρ target : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (htarget : 0 < target) : ρ ^ geometricCeiling ρ target ≤ target := by
  apply (Real.log_le_log_iff (pow_pos hρ _) htarget).mp
  rw [Real.log_pow]
  have hn := Nat.le_ceil (Real.log target / Real.log ρ)
  have hl := Real.log_neg hρ hρ1
  have hm := mul_le_mul_of_nonpos_right hn hl.le
  rw [div_mul_cancel₀ _ (ne_of_lt hl)] at hm
  exact hm

theorem geometricCeiling_le (ρ target : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (htarget : 0 < target) (htarget1 : target ≤ 1) :
    (geometricCeiling ρ target : ℝ) ≤ Real.log target / Real.log ρ + 1 := by
  apply (Nat.ceil_lt_add_one _).le
  exact div_nonneg_of_nonpos (Real.log_nonpos htarget.le htarget1)
    (Real.log_neg hρ hρ1).le

private theorem exists_rational_geometric (ρ target : ℚ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (htarget : 0 < target) : ∃ n : ℕ, ρ ^ n ≤ target := by
  refine ⟨geometricCeiling ρ target, ?_⟩
  exact_mod_cast pow_geometricCeiling_le (ρ : ℝ) target
    (by exact_mod_cast hρ) (by exact_mod_cast hρ1) (by exact_mod_cast htarget)

/-- The executable least natural exponent satisfying a rational stopping test. -/
def geometricSteps (ρ target : ℚ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (htarget : 0 < target) : ℕ :=
  Nat.find (exists_rational_geometric ρ target hρ hρ1 htarget)

theorem geometricSteps_spec (ρ target : ℚ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (htarget : 0 < target) : ρ ^ geometricSteps ρ target hρ hρ1 htarget ≤ target :=
  Nat.find_spec (exists_rational_geometric ρ target hρ hρ1 htarget)

theorem geometricSteps_le_log (ρ target : ℚ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (htarget : 0 < target) (htarget1 : target ≤ 1) :
    (geometricSteps ρ target hρ hρ1 htarget : ℝ) ≤
      Real.log (target : ℝ) / Real.log (ρ : ℝ) + 1 := by
  have hn : geometricSteps ρ target hρ hρ1 htarget ≤ geometricCeiling ρ target := by
    apply Nat.find_min'
    exact_mod_cast pow_geometricCeiling_le (ρ : ℝ) target
      (by exact_mod_cast hρ) (by exact_mod_cast hρ1) (by exact_mod_cast htarget)
  exact (by exact_mod_cast hn : (geometricSteps ρ target hρ hρ1 htarget : ℝ) ≤
    geometricCeiling ρ target).trans
      (geometricCeiling_le ρ target (by exact_mod_cast hρ) (by exact_mod_cast hρ1)
        (by exact_mod_cast htarget) (by exact_mod_cast htarget1))

/-- Fixed rational platform bounds. These are the certified physical rates
and constants, independent of the sparse input and of every random draw. -/
structure SpacingPlatform where
  r : ℚ
  a : ℚ
  c : ℚ
  errorConstant : ℚ
  minimumDistance : ℕ
  r_pos : 0 < r
  r_lt_one : r < 1
  a_pos : 0 < a
  a_lt_one : a < 1
  rates_separated : r^2 < a
  c_pos : 0 < c
  errorConstant_ge_one : 1 ≤ errorConstant

namespace SpacingPlatform

def ratio (P : SpacingPlatform) : ℚ := P.r^2 / P.a

theorem ratio_pos (P : SpacingPlatform) : 0 < P.ratio :=
  div_pos (pow_pos P.r_pos _) P.a_pos

theorem ratio_lt_one (P : SpacingPlatform) : P.ratio < 1 := by
  exact (div_lt_one P.a_pos).mpr P.rates_separated

def weight (P : SpacingPlatform) : ℚ := max 1 (16384 * P.errorConstant / P.c)

theorem weight_ge_one (P : SpacingPlatform) : 1 ≤ P.weight := le_max_left _ _
theorem weight_pos (P : SpacingPlatform) : 0 < P.weight := lt_of_lt_of_le zero_lt_one P.weight_ge_one

def fixedFloor (P : SpacingPlatform) : ℕ := max P.minimumDistance
  (geometricSteps P.r (1/2) P.r_pos P.r_lt_one (by norm_num))

/-- Only a rational power comparison is used by the input-dependent search. -/
def spacing (P : SpacingPlatform) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) : ℕ :=
  max P.fixedFloor (geometricSteps P.ratio (ε / (P.weight * K))
    P.ratio_pos P.ratio_lt_one (div_pos hε (mul_pos P.weight_pos hK)))

def zeta (P : SpacingPlatform) (d : ℕ) : ℚ := P.r ^ d
def alpha (P : SpacingPlatform) (d : ℕ) : ℚ := (P.c / 4) * P.a ^ d

theorem spacing_minimum (P : SpacingPlatform) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    P.minimumDistance ≤ P.spacing K ε hK hε :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem zeta_pos (P : SpacingPlatform) (d : ℕ) : 0 < P.zeta d := pow_pos P.r_pos _
theorem alpha_pos (P : SpacingPlatform) (d : ℕ) : 0 < P.alpha d :=
  mul_pos (div_pos P.c_pos (by norm_num)) (pow_pos P.a_pos _)

theorem spacing_zeta_le_half (P : SpacingPlatform) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    P.zeta (P.spacing K ε hK hε) ≤ 1/2 := by
  apply le_trans _ (geometricSteps_spec P.r (1/2) P.r_pos P.r_lt_one (by norm_num))
  apply (pow_le_pow_iff_right_of_lt_one₀ P.r_pos P.r_lt_one).mpr
  exact (le_max_right _ _).trans (le_max_left _ _)

theorem spacing_ratio_bound (P : SpacingPlatform) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    P.ratio ^ P.spacing K ε hK hε ≤ ε / (P.weight * K) := by
  apply le_trans _ (geometricSteps_spec P.ratio (ε / (P.weight * K))
    P.ratio_pos P.ratio_lt_one (div_pos hε (mul_pos P.weight_pos hK)))
  exact (pow_le_pow_iff_right_of_lt_one₀ P.ratio_pos P.ratio_lt_one).mpr (le_max_right _ _)

/-- The literal bright-block error budget, with the paper's constant4096. -/
theorem spacing_error_budget (P : SpacingPlatform) (K ε : ℚ) (hK : 0 < K) (hε : 0 < ε) :
    P.errorConstant * (P.zeta (P.spacing K ε hK hε))^2 ≤
      P.alpha (P.spacing K ε hK hε) * ε / (4096 * K) := by
  let d := P.spacing K ε hK hε
  have hp := P.spacing_ratio_bound K ε hK hε
  have hr : P.ratio^d = (P.zeta d)^2 / P.a^d := by
    simp only [ratio, zeta, div_pow]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 d]
  change P.ratio ^ d ≤ _ at hp
  rw [hr] at hp
  have ha := pow_pos P.a_pos d
  have hw := le_max_right (1 : ℚ) (16384 * P.errorConstant / P.c)
  change 16384 * P.errorConstant / P.c ≤ P.weight at hw
  have hw' : 16384 * P.errorConstant ≤ P.weight * P.c := (div_le_iff₀ P.c_pos).mp hw
  have hp' : (P.zeta d)^2 * (P.weight * K) ≤ ε * P.a^d :=
    (div_le_div_iff₀ ha (mul_pos P.weight_pos hK)).mp hp
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℚ)<4096) hK)).mpr
  change P.errorConstant * (P.zeta d)^2 * (4096*K) ≤ (P.c/4*P.a^d)*ε
  have hz : 0 ≤ (P.zeta d)^2 * K := mul_nonneg (sq_nonneg _) hK.le
  have hmul := mul_le_mul_of_nonneg_right hw' hz
  have hcp := mul_le_mul_of_nonneg_left hp' P.c_pos.le
  nlinarith

/-- The interaction square is smaller than the nearest-neighbor scale. -/
theorem spacing_zeta_sq_le_alpha (P : SpacingPlatform) (K ε : ℚ)
    (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (P.zeta (P.spacing K ε (by linarith) hε))^2 ≤
      P.alpha (P.spacing K ε (by linarith) hε) := by
  have h := P.spacing_error_budget K ε (by linarith) hε
  have ha := P.alpha_pos (P.spacing K ε (by linarith) hε)
  have hden : 1 ≤ 4096*K := by linarith
  have he : ε / (4096*K) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  calc
    _ ≤ P.errorConstant * (P.zeta (P.spacing K ε (by linarith) hε))^2 :=
      le_mul_of_one_le_left (sq_nonneg _) P.errorConstant_ge_one
    _ ≤ _ := h
    _ = P.alpha (P.spacing K ε (by linarith) hε) * (ε / (4096*K)) := by ring
    _ ≤ _ := mul_le_of_le_one_right ha.le he

/-- A positive fixed denominator for every logarithmic resource bound. -/
noncomputable def decayLog (P : SpacingPlatform) : ℝ := -Real.log (P.ratio : ℝ)

theorem decayLog_pos (P : SpacingPlatform) : 0 < P.decayLog := by
  exact neg_pos.mpr (Real.log_neg (by exact_mod_cast P.ratio_pos)
    (by exact_mod_cast P.ratio_lt_one))

/-- The rational search has a literal logarithmic upper bound. -/
theorem spacing_le_logs (P : SpacingPlatform) (K ε : ℚ)
    (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (P.spacing K ε (by linarith) hε : ℝ) ≤
      P.fixedFloor + 1 +
        (Real.log (P.weight : ℝ) + Real.log (K : ℝ) + Real.log (ε : ℝ)⁻¹) / P.decayLog := by
  have hKpos : (0 : ℚ) < K := by linarith
  have ht1 : ε / (P.weight * K) ≤ 1 := by
    apply (div_le_one (mul_pos P.weight_pos hKpos)).mpr
    exact hε1.trans (one_le_mul_of_one_le_of_one_le P.weight_ge_one hK)
  have hs := geometricSteps_le_log P.ratio (ε / (P.weight*K)) P.ratio_pos
    P.ratio_lt_one (div_pos hε (mul_pos P.weight_pos hKpos)) ht1
  have he : Real.log ((ε / (P.weight*K) : ℚ) : ℝ) / Real.log (P.ratio : ℝ) =
      (Real.log (P.weight : ℝ) + Real.log (K : ℝ) + Real.log (ε : ℝ)⁻¹) / P.decayLog := by
    push_cast
    rw [Real.log_div (by exact_mod_cast ne_of_gt hε)
      (by exact_mod_cast ne_of_gt (mul_pos P.weight_pos hKpos)),
      Real.log_mul (by exact_mod_cast ne_of_gt P.weight_pos) (by exact_mod_cast ne_of_gt hKpos),
      Real.log_inv]
    unfold decayLog
    ring
  rw [he] at hs
  have hn : P.spacing K ε hKpos hε ≤ P.fixedFloor +
      geometricSteps P.ratio (ε / (P.weight*K)) P.ratio_pos
        P.ratio_lt_one (div_pos hε (mul_pos P.weight_pos hKpos)) := by unfold spacing; omega
  have hnr : (P.spacing K ε hKpos hε : ℝ) ≤ P.fixedFloor +
      (geometricSteps P.ratio (ε / (P.weight*K)) P.ratio_pos
        P.ratio_lt_one (div_pos hε (mul_pos P.weight_pos hKpos)) : ℝ) := by exact_mod_cast hn
  linarith

/-- Polynomial logical budgets give the paper's fixed affine logarithmic
spacing bound, with all constant factors retained explicitly. -/
theorem spacing_le_log_input (P : SpacingPlatform) (K ε : ℚ)
    (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m K₀ E₀ β χ : ℝ) (hm : 0 < m) (hK₀ : 0 < K₀) (hE₀ : 0 < E₀)
    (hKb : (K : ℝ) ≤ K₀ * m^β) (hEb : (ε : ℝ)⁻¹ ≤ E₀ * m^χ) :
    (P.spacing K ε (by linarith) hε : ℝ) ≤
      (P.fixedFloor + 1 + (Real.log (P.weight : ℝ) + Real.log K₀ + Real.log E₀) / P.decayLog) +
        ((β+χ)/P.decayLog)*Real.log m := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show (0:ℚ)<K by linarith)
  have hEr : (0 : ℝ) < (ε : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hε)
  have hk := Real.log_le_log hKr hKb
  have he := Real.log_le_log hEr hEb
  rw [Real.log_mul (ne_of_gt hK₀) (ne_of_gt (Real.rpow_pos_of_pos hm β)), Real.log_rpow hm] at hk
  rw [Real.log_mul (ne_of_gt hE₀) (ne_of_gt (Real.rpow_pos_of_pos hm χ)), Real.log_rpow hm] at he
  apply (P.spacing_le_logs K ε hK hε hε1).trans
  have hadd := add_le_add (add_le_add (le_refl (Real.log (P.weight : ℝ))) hk) he
  have hd := div_le_div_of_nonneg_right hadd P.decayLog_pos.le
  calc
    _ ≤ P.fixedFloor + 1 +
      (Real.log (P.weight : ℝ) + (Real.log K₀ + β*Real.log m) +
        (Real.log E₀ + χ*Real.log m)) / P.decayLog := add_le_add (le_refl _) hd
    _ = _ := by ring

end SpacingPlatform

/-- Logarithmic separation preserves inverse-polynomial geometric scales. -/
theorem geometric_inverse_from_spacing (r m D₀ D₁ : ℝ) (d : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hm : 0 < m)
    (hd : (d : ℝ) ≤ D₀ + D₁ * Real.log m) :
    (r^d)⁻¹ ≤ Real.exp (D₀ * -Real.log r) * m^(D₁ * -Real.log r) := by
  apply (Real.log_le_log_iff (inv_pos.mpr (pow_pos hr _))
    (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hm _))).mp
  rw [Real.log_inv, Real.log_pow,
    Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.rpow_pos_of_pos hm _)),
    Real.log_exp, Real.log_rpow hm]
  have h := mul_le_mul_of_nonneg_right hd (neg_nonneg.mpr (Real.log_neg hr hr1).le)
  nlinarith

namespace SpacingPlatform

/-- Explicit fixed constants in the input-size spacing estimate. -/
noncomputable def logConstant (P : SpacingPlatform) (K₀ E₀ : ℝ) : ℝ :=
  P.fixedFloor + 1 + (Real.log (P.weight : ℝ) + Real.log K₀ + Real.log E₀) / P.decayLog

noncomputable def logExponent (P : SpacingPlatform) (β χ : ℝ) : ℝ := (β + χ) / P.decayLog

/-- Both geometric scales have explicit polynomial reciprocal bounds for the
actual selected integer spacing. No successful spacing is assumed. -/
theorem selected_scale_inverse_bounds (P : SpacingPlatform) (K ε : ℚ)
    (hK : 1 ≤ K) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m K₀ E₀ β χ : ℝ) (hm : 0 < m) (hK₀ : 0 < K₀) (hE₀ : 0 < E₀)
    (hKb : (K : ℝ) ≤ K₀ * m^β) (hEb : (ε : ℝ)⁻¹ ≤ E₀ * m^χ) :
    ((P.zeta (P.spacing K ε (by linarith) hε) : ℚ) : ℝ)⁻¹ ≤
        Real.exp (P.logConstant K₀ E₀ * -Real.log (P.r : ℝ)) *
          m^(P.logExponent β χ * -Real.log (P.r : ℝ)) ∧
    ((P.alpha (P.spacing K ε (by linarith) hε) : ℚ) : ℝ)⁻¹ ≤
        (4 / (P.c : ℝ)) * Real.exp (P.logConstant K₀ E₀ * -Real.log (P.a : ℝ)) *
          m^(P.logExponent β χ * -Real.log (P.a : ℝ)) := by
  let d := P.spacing K ε (by linarith) hε
  have hd : (d : ℝ) ≤ P.logConstant K₀ E₀ + P.logExponent β χ * Real.log m :=
    P.spacing_le_log_input K ε hK hε hε1 m K₀ E₀ β χ hm hK₀ hE₀ hKb hEb
  constructor
  · simpa only [zeta, Rat.cast_pow] using geometric_inverse_from_spacing (P.r : ℝ)
      m (P.logConstant K₀ E₀) (P.logExponent β χ) d
      (by exact_mod_cast P.r_pos) (by exact_mod_cast P.r_lt_one) hm hd
  · have ha := geometric_inverse_from_spacing (P.a : ℝ)
      m (P.logConstant K₀ E₀) (P.logExponent β χ) d
      (by exact_mod_cast P.a_pos) (by exact_mod_cast P.a_lt_one) hm hd
    have hc : (0 : ℝ) ≤ 4 / (P.c : ℝ) := div_nonneg (by norm_num) (by exact_mod_cast P.c_pos.le)
    have ht := mul_le_mul_of_nonneg_left ha hc
    simpa only [alpha, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
      mul_inv_rev, inv_div, d, mul_assoc, mul_left_comm, mul_comm] using ht

end SpacingPlatform

end Maxwell.Realization
