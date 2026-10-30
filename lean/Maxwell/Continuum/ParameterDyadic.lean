import Maxwell.Realization.Precision

/-! Literal rational master constants, detuning dyadics, and rational
floor-exponential tests for the continuum parameter algorithm.

The searches and stopping tests in this module are executable. -/

namespace Maxwell.Continuum.Parameters

def slowDivisor : ℕ := 2^1024
def mastercs : ℚ := 1/(slowDivisor : ℚ)
theorem slowDivisor_pos : 0 < slowDivisor := by unfold slowDivisor; positivity

def zeta (d : ℕ) : ℚ := (1/3)^d
def alpha (L d : ℕ) : ℚ := ((2 : ℚ)^1026)⁻¹*(L : ℚ)^2*(1/8)^d

theorem zeta_pos (d : ℕ) : 0 < zeta d := by unfold zeta; positivity
theorem zeta_le_one (d : ℕ) : zeta d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
theorem alpha_pos {L : ℕ} (hL : 0 < L) (d : ℕ) : 0 < alpha L d := by
  unfold alpha
  have hp : (0 : ℚ) < L := by exact_mod_cast hL
  positivity

def tauBudget (L d : ℕ) : ℚ := (zeta d)^2/((2 : ℚ)^24*(L : ℚ)^4)

theorem tauBudget_pos {L : ℕ} (hL : 0 < L) (d : ℕ) : 0 < tauBudget L d := by
  have hz := zeta_pos d
  have hp : (0 : ℚ) < L := by exact_mod_cast hL
  unfold tauBudget
  positivity

theorem tauBudget_le_one {L : ℕ} (hL : 0 < L) (d : ℕ) : tauBudget L d ≤ 1 := by
  have hL1 : (1 : ℚ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hden : (1 : ℚ) ≤ (2 : ℚ)^24*(L : ℚ)^4 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hL1)
  apply (div_le_one (lt_of_lt_of_le zero_lt_one hden)).mpr
  exact (pow_le_one₀ (zeta_pos d).le (zeta_le_one d)).trans hden

def tau (L d : ℕ) (hL : 0 < L) : ℚ :=
  Realization.precisionUnit (tauBudget L d) (tauBudget_pos hL d)

theorem tau_pos (L d : ℕ) (hL : 0 < L) : 0 < tau L d hL :=
  Realization.precisionUnit_pos _ _

theorem tau_bracket (L d : ℕ) (hL : 0 < L) :
    (zeta d)^2/((2 : ℚ)^25*(L : ℚ)^4) < tau L d hL ∧ tau L d hL ≤ tauBudget L d := by
  constructor
  · have he := Realization.precisionUnit_lower (tauBudget L d) (tauBudget_pos hL d)
    rw [Realization.precisionBudget, min_eq_right (tauBudget_le_one hL d)] at he
    change tauBudget L d/2 < tau L d hL at he
    convert he using 1
    unfold tauBudget
    norm_num
    ring
  · exact Realization.precisionUnit_le _ _

theorem tau_inverse_bound (L d : ℕ) (hL : 0 < L) :
    (tau L d hL)⁻¹ < (2 : ℚ)^25*(L : ℚ)^4*(3 : ℚ)^(2*d) := by
  have hz := zeta_pos d
  have hp : (0 : ℚ) < L := by exact_mod_cast hL
  have he := (inv_lt_inv₀ (tau_pos L d hL)
    (show (0 : ℚ) < (zeta d)^2/((2 : ℚ)^25*(L : ℚ)^4) by positivity)).mpr (tau_bracket L d hL).1
  convert he using 1
  simp only [inv_div, zeta, div_pow, one_pow, div_div, div_one, ← pow_mul]
  rw [Nat.mul_comm d 2]
  ring

def rationalDecay (t : ℕ) : ℚ := (1/2)^(t/slowDivisor)

theorem rationalDecay_pos (t : ℕ) : 0 < rationalDecay t := by unfold rationalDecay; positivity
theorem rationalDecay_le_one (t : ℕ) : rationalDecay t ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem decay_floor_le (t : ℕ) : ((t/slowDivisor : ℕ) : ℝ) ≤ (mastercs : ℝ)*(t : ℝ) := by
  have hd : (0 : ℝ) < slowDivisor := by exact_mod_cast slowDivisor_pos
  have he : ((t/slowDivisor : ℕ) : ℝ)*(slowDivisor : ℝ) ≤ t := by
    exact_mod_cast Nat.div_mul_le_self t slowDivisor
  have hf := (le_div_iff₀ hd).mpr he
  simpa only [mastercs, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    Rat.cast_mul, Rat.cast_inv, one_div, div_eq_mul_inv, mul_comm, mul_one] using hf

theorem exponential_le_rationalDecay (t : ℕ) :
    Real.exp (-(mastercs : ℝ)*(t : ℝ)) ≤ (rationalDecay t : ℝ) := by
  have hf := decay_floor_le t
  have hl : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hn : (0 : ℝ) ≤ (t/slowDivisor : ℕ) := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hl hn
  have he : Real.exp (-(mastercs : ℝ)*(t : ℝ)) ≤ Real.exp (((t/slowDivisor : ℕ) : ℝ)*(-Real.log 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hf, hm]
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  simpa only [rationalDecay, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_inv, Rat.cast_natCast, one_div] using he

theorem rational_test_implies_exponential {A B : ℚ} (hA : 0 ≤ A) (t : ℕ)
    (htest : A*rationalDecay t ≤ B) : (A : ℝ)*Real.exp (-(mastercs : ℝ)*(t : ℝ)) ≤ B := by
  exact (mul_le_mul_of_nonneg_left (exponential_le_rationalDecay t)
    (by exact_mod_cast hA)).trans (by exact_mod_cast htest)

#print axioms tau_bracket
#print axioms exponential_le_rationalDecay

end Maxwell.Continuum.Parameters
