import Maxwell.Realization.Spacing
import Maxwell.Interfaces
import Maxwell.Logical.Rounding
import Maxwell.Target

/-! Executable dyadic precision selection and literal polynomial absorption.
The selection tests rational inequalities only; logarithms are used solely
in its proved resource bound. -/
namespace Maxwell.Realization

/-- Cap a positive error budget at one before selecting its dyadic unit. -/
def precisionBudget (budget : ℚ) : ℚ := min 1 budget

theorem precisionBudget_pos (budget : ℚ) (hbudget : 0 < budget) :
    0 < precisionBudget budget := lt_min (by norm_num) hbudget

/-- The first binary precision whose unit is within the supplied budget. -/
def precisionBits (budget : ℚ) (hbudget : 0 < budget) : ℕ :=
  geometricSteps (1/2) (precisionBudget budget) (by norm_num) (by norm_num)
    (precisionBudget_pos budget hbudget)

def precisionUnit (budget : ℚ) (hbudget : 0 < budget) : ℚ :=
  1 / 2 ^ precisionBits budget hbudget

theorem precisionUnit_eq_pow (budget : ℚ) (hbudget : 0 < budget) :
    precisionUnit budget hbudget = (1/2 : ℚ) ^ precisionBits budget hbudget := by
  simp [precisionUnit]

theorem precisionUnit_pos (budget : ℚ) (hbudget : 0 < budget) :
    0 < precisionUnit budget hbudget := by unfold precisionUnit; positivity

theorem precisionUnit_le_budget (budget : ℚ) (hbudget : 0 < budget) :
    precisionUnit budget hbudget ≤ precisionBudget budget := by
  rw [precisionUnit_eq_pow]
  exact geometricSteps_spec _ _ _ _ _

theorem precisionUnit_le (budget : ℚ) (hbudget : 0 < budget) :
    precisionUnit budget hbudget ≤ budget :=
  (precisionUnit_le_budget budget hbudget).trans (min_le_right _ _)

theorem precisionUnit_le_one (budget : ℚ) (hbudget : 0 < budget) :
    precisionUnit budget hbudget ≤ 1 :=
  (precisionUnit_le_budget budget hbudget).trans (min_le_left _ _)

/-- Minimality prevents any unnecessary loss of precision beyond a factor two. -/
theorem precisionUnit_lower (budget : ℚ) (hbudget : 0 < budget) :
    precisionBudget budget / 2 < precisionUnit budget hbudget := by
  rw [precisionUnit_eq_pow]
  cases hn : precisionBits budget hbudget with
  | zero =>
    simp only [pow_zero]
    have h := min_le_left (1 : ℚ) budget
    change precisionBudget budget ≤ 1 at h
    linarith
  | succ n =>
    have hprev : precisionBudget budget < (1/2 : ℚ)^n := by
      apply lt_of_not_ge
      have hlt : n < precisionBits budget hbudget := by omega
      exact Nat.find_min _ hlt
    rw [pow_succ]
    linarith

/-- The real-valued estimate bounds an executable rational search. -/
theorem precisionBits_le_log (budget : ℚ) (hbudget : 0 < budget) :
    (precisionBits budget hbudget : ℝ) ≤
      1 + Real.log ((precisionBudget budget : ℝ)⁻¹) / Real.log 2 := by
  have h := geometricSteps_le_log (1/2) (precisionBudget budget)
    (by norm_num) (by norm_num) (precisionBudget_pos budget hbudget) (min_le_left _ _)
  change (precisionBits budget hbudget : ℝ) ≤ _ at h
  have heq : Real.log (precisionBudget budget : ℝ) / Real.log ((1/2 : ℚ) : ℝ) + 1 =
      1 + Real.log ((precisionBudget budget : ℝ)⁻¹) / Real.log 2 := by
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, Real.log_inv]
    ring
  exact h.trans_eq heq

/-- The selected dyadic has the canonical one-bit numerator. -/
def selectedDyadic (budget : ℚ) (hbudget : 0 < budget) :
    Maxwell.Dyadic (precisionBits budget hbudget) := ⟨1⟩

theorem selectedDyadic_value (budget : ℚ) (hbudget : 0 < budget) :
    (selectedDyadic budget hbudget).value = precisionUnit budget hbudget := by
  simp [selectedDyadic, Maxwell.Dyadic.value, precisionUnit]

/-- Inverting the selected unit costs at most twice the capped inverse budget. -/
theorem precisionUnit_inverse (budget : ℚ) (hbudget : 0 < budget) :
    (precisionUnit budget hbudget)⁻¹ < 2 * (precisionBudget budget)⁻¹ := by
  have h := precisionUnit_lower budget hbudget
  have hpos := precisionBudget_pos budget hbudget
  have hi := (inv_lt_inv₀ (precisionUnit_pos budget hbudget) (div_pos hpos (by norm_num))).mpr h
  convert hi using 1
  field_simp

/-- A literal logarithm bound valid throughout the non-base input range. -/
theorem log_two_add_le (m : ℝ) (hm : 2 ≤ m) : Real.log (2+m) ≤ m := by
  have hmpos : 0 < m := by linarith
  have h := Real.log_le_log (by linarith : 0 < 2+m) (show 2+m ≤ 2*m by linarith)
  rw [Real.log_mul (by norm_num) (ne_of_gt hmpos)] at h
  have htwo := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have hlog := Real.log_le_sub_one_of_pos hmpos
  linarith

/-- A rationally computable integer exponent absorbs any fixed rational
coefficient and rational polynomial exponent, including all logarithms. -/
def absorptionExponent (K a : ℚ) (b : ℕ) : ℕ := ⌈K⌉₊ + ⌈a⌉₊ + b

private theorem nat_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ]
    have hp : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    linarith

/-- The bound has coefficient exactly one and holds for every input m≥2,
so there is no uncharged asymptotic threshold in the construction. -/
theorem polynomial_log_absorption (K a : ℚ) (b : ℕ) (m : ℝ)
    (hm : 2 ≤ m) :
    (K : ℝ) * m^(a : ℝ) * (Real.log (2+m))^b ≤
      m^(absorptionExponent K a b) := by
  have hmpos : 0 < m := by linarith
  have hmone : 1 ≤ m := by linarith
  have hKceil : (K : ℝ) ≤ (⌈K⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil K
  have haceil : (a : ℝ) ≤ (⌈a⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil a
  have hcoef : (K : ℝ) ≤ m^⌈K⌉₊ :=
    hKceil.trans ((nat_le_two_pow _).trans (pow_le_pow_left₀ (by norm_num) hm _))
  have hexp : m^(a : ℝ) ≤ m^⌈a⌉₊ := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hmone haceil
  have hlogpos : 0 ≤ Real.log (2+m) := Real.log_nonneg (by linarith)
  have hlog : (Real.log (2+m))^b ≤ m^b :=
    pow_le_pow_left₀ hlogpos (log_two_add_le m hm) _
  calc
    _ ≤ (m^⌈K⌉₊ * m^⌈a⌉₊) * m^b :=
      mul_le_mul (mul_le_mul hcoef hexp (Real.rpow_nonneg hmpos.le _) (by positivity))
        hlog (pow_nonneg hlogpos _) (by positivity)
    _ = _ := by unfold absorptionExponent; rw [pow_add, pow_add]

/-- Actual rational nearest-grid rounding at the selected precision. -/
def selectedRound (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    Maxwell.Dyadic (precisionBits budget hbudget) :=
  Maxwell.Logical.Rounding.nearest (precisionBits budget hbudget) x

/-- The selected precision gives half a unit of nearest-grid error. -/
theorem selectedRound_error_unit (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    |(selectedRound budget hbudget x).value - x| ≤ precisionUnit budget hbudget / 2 := by
  calc
    _ ≤ 1 / (2 * (2 : ℚ)^precisionBits budget hbudget) :=
      Maxwell.Logical.Rounding.nearest_error (precisionBits budget hbudget) x
    _ = _ := by unfold precisionUnit; ring

theorem selectedRound_error (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    |(selectedRound budget hbudget x).value - x| ≤ budget / 2 := by
  exact (selectedRound_error_unit budget hbudget x).trans
    (div_le_div_of_nonneg_right (precisionUnit_le budget hbudget) (by norm_num))

/-- A canonical fixed-denominator dyadic is returned on every rational input. -/
theorem selectedRound_value (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    (selectedRound budget hbudget x).value =
      ((selectedRound budget hbudget x).numerator : ℚ) / 2 ^ precisionBits budget hbudget := rfl

theorem selectedRound_abs_le (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    |(selectedRound budget hbudget x).value| ≤ |x| + 1 / 2 := by
  calc
    _ = |((selectedRound budget hbudget x).value - x) + x| := by congr 1; ring
    _ ≤ |(selectedRound budget hbudget x).value - x| + |x| := abs_add_le _ _
    _ ≤ _ := by linarith [selectedRound_error_unit budget hbudget x, precisionUnit_le_one budget hbudget]

theorem selectedRound_numerator_bound (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    |((selectedRound budget hbudget x).numerator : ℚ)| ≤
      (|x| + 1 / 2) * 2 ^ precisionBits budget hbudget := by
  have he : ((selectedRound budget hbudget x).numerator : ℚ) =
      (selectedRound budget hbudget x).value * 2 ^ precisionBits budget hbudget := by
    rw [selectedRound_value]
    field_simp
  rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ precisionBits budget hbudget)]
  exact mul_le_mul_of_nonneg_right (selectedRound_abs_le budget hbudget x) (by positivity)

private theorem unsignedBitLength_le_of_lt_pow {n k : ℕ} (h : n < 2^k) :
    Maxwell.unsignedBitLength n ≤ k := by
  by_cases hn : n = 0
  · simp [Maxwell.unsignedBitLength, hn]
  · have hh := (Nat.log2_lt hn).mpr h
    simp only [Maxwell.unsignedBitLength, hn, ↓reduceIte]
    omega

/-- The stored numerator needs at most the integer range plus precision and
two sign/rounding bits. -/
theorem selectedRound_numeratorBits (budget : ℚ) (hbudget : 0 < budget)
    (x : ℚ) (integerBits : ℕ) (hx : |x| ≤ (2 : ℚ)^integerBits) :
    (selectedRound budget hbudget x).numeratorBits ≤
      integerBits + precisionBits budget hbudget + 2 := by
  have hp : (0 : ℚ) < 2 ^ precisionBits budget hbudget := by positivity
  have hk : (1 : ℚ) ≤ 2^integerBits := one_le_pow₀ (by norm_num)
  have hnum : |((selectedRound budget hbudget x).numerator : ℚ)| <
      (2 : ℚ)^(integerBits + precisionBits budget hbudget + 1) := by
    calc
      _ ≤ (|x| + 1 / 2) * 2 ^ precisionBits budget hbudget :=
        selectedRound_numerator_bound budget hbudget x
      _ < (2^integerBits + 2^integerBits) * 2 ^ precisionBits budget hbudget :=
        mul_lt_mul_of_pos_right (by linarith) hp
      _ = _ := by rw [pow_add, pow_add]; ring
  have hn : (selectedRound budget hbudget x).numerator.natAbs <
      2^(integerBits + precisionBits budget hbudget + 1) := by
    have hcast : ((selectedRound budget hbudget x).numerator.natAbs : ℚ) <
        (2 : ℚ)^(integerBits + precisionBits budget hbudget + 1) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hnum
    exact_mod_cast hcast
  have hh := unsignedBitLength_le_of_lt_pow hn
  unfold Maxwell.Dyadic.numeratorBits Maxwell.signedBitLength
  omega

theorem selectedRound_denominatorBits (budget : ℚ) (hbudget : 0 < budget) :
    Maxwell.unsignedBitLength (2 ^ precisionBits budget hbudget) = precisionBits budget hbudget + 1 :=
  Maxwell.Dyadic.denominator_bitLength _

/-- The full stored dyadic has a linear representation bound. -/
theorem selectedRound_representationBits (budget : ℚ) (hbudget : 0 < budget)
    (x : ℚ) (integerBits : ℕ) (hx : |x| ≤ (2 : ℚ)^integerBits) :
    (selectedRound budget hbudget x).numeratorBits +
      Maxwell.unsignedBitLength (2 ^ precisionBits budget hbudget) ≤
      integerBits + 2 * precisionBits budget hbudget + 3 := by
  rw [selectedRound_denominatorBits]
  have h := selectedRound_numeratorBits budget hbudget x integerBits hx
  omega

/-- One guard integer bit places every selected rounded value strictly inside
the emitted fixed-width format. -/
theorem selectedRound_inRange (budget : ℚ) (hbudget : 0 < budget)
    (x : ℚ) (integerBits : ℕ) (hx : |x| ≤ (2 : ℚ)^integerBits) :
    (Maxwell.Target.FixedPointFormat.mk (integerBits + 1) (precisionBits budget hbudget)).InRange
      ((selectedRound budget hbudget x).value : ℝ) := by
  have h : |(selectedRound budget hbudget x).value| < (2 : ℚ)^(integerBits + 1) := by
    have hk : (1 : ℚ) ≤ 2^integerBits := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith [selectedRound_abs_le budget hbudget x]
  have hr : |((selectedRound budget hbudget x).value : ℝ)| < (2 : ℝ)^(integerBits + 1) := by
    exact_mod_cast h
  exact ⟨(abs_lt.mp hr).1.le, (abs_lt.mp hr).2⟩

/-- A polynomial inverse-budget estimate gives the required logarithmic word
width, including the cap used by the actual selector. -/
theorem precisionBits_le_polynomial (budget : ℚ) (hbudget : 0 < budget)
    (A B m : ℝ) (hA : 1 ≤ A) (hB : 0 ≤ B) (hm : 1 ≤ m)
    (hbound : (budget : ℝ)⁻¹ ≤ A * m^B) :
    (precisionBits budget hbudget : ℝ) ≤
      1 + (Real.log A + B * Real.log m) / Real.log 2 := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hpow : 1 ≤ m^B := Real.one_le_rpow hm hB
  have hcap : (precisionBudget budget : ℝ)⁻¹ ≤ A * m^B := by
    by_cases hb : budget ≤ 1
    · simpa only [precisionBudget, min_eq_right hb] using hbound
    · have hmin : precisionBudget budget = 1 := min_eq_left (le_of_not_ge hb)
      rw [hmin]
      norm_num only [Rat.cast_one, inv_one]
      exact one_le_mul_of_one_le_of_one_le hA hpow
  have hcap0 : (0 : ℝ) < (precisionBudget budget : ℝ)⁻¹ := by
    have hh : (0 : ℝ) < (precisionBudget budget : ℝ) := by
      exact_mod_cast precisionBudget_pos budget hbudget
    positivity
  have hlog := Real.log_le_log hcap0 hcap
  rw [Real.log_mul hA0.ne' (Real.rpow_pos_of_pos hm0 B).ne', Real.log_rpow hm0] at hlog
  exact (precisionBits_le_log budget hbudget).trans
    (add_le_add (le_refl 1)
      (div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le))

/-- Reducing a dyadic rational cannot enlarge its denominator. -/
theorem selectedRound_reduced_den_le (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    (selectedRound budget hbudget x).value.den ≤ 2 ^ precisionBits budget hbudget := by
  have hd := Rat.den_dvd (selectedRound budget hbudget x).numerator
    ((2 : ℤ)^precisionBits budget hbudget)
  have he : Rat.divInt (selectedRound budget hbudget x).numerator
      ((2 : ℤ)^precisionBits budget hbudget) = (selectedRound budget hbudget x).value := by
    rw [Rat.divInt_eq_div, selectedRound_value]
    simp
  rw [he] at hd
  have hn : (selectedRound budget hbudget x).value.den ∣ 2 ^ precisionBits budget hbudget := by
    exact_mod_cast hd
  exact Nat.le_of_dvd (by positivity) hn

/-- The reduced numerator in the serialized rational has the same bit bound
as the fixed-denominator representation. -/
theorem selectedRound_reduced_numeratorBits (budget : ℚ) (hbudget : 0 < budget)
    (x : ℚ) (integerBits : ℕ) (hx : |x| ≤ (2 : ℚ)^integerBits) :
    Maxwell.signedBitLength (selectedRound budget hbudget x).value.num ≤
      integerBits + precisionBits budget hbudget + 2 := by
  let q := (selectedRound budget hbudget x).value
  have hp : (0 : ℚ) < 2 ^ precisionBits budget hbudget := by positivity
  have hk : (1 : ℚ) ≤ 2^integerBits := one_le_pow₀ (by norm_num)
  have hden : (q.den : ℚ) ≤ 2 ^ precisionBits budget hbudget := by
    exact_mod_cast selectedRound_reduced_den_le budget hbudget x
  have hnum : |(q.num : ℚ)| < (2 : ℚ)^(integerBits + precisionBits budget hbudget + 1) := by
    calc
      _ = |q| * q.den := by rw [← Rat.mul_den_eq_num, abs_mul, abs_of_nonneg (show (0 : ℚ) ≤ (q.den : ℚ) by positivity)]
      _ ≤ (|x| + 1 / 2) * 2 ^ precisionBits budget hbudget :=
        mul_le_mul (selectedRound_abs_le budget hbudget x) hden (Nat.cast_nonneg _) (by positivity)
      _ < (2^integerBits + 2^integerBits) * 2 ^ precisionBits budget hbudget :=
        mul_lt_mul_of_pos_right (by linarith) hp
      _ = _ := by rw [pow_add, pow_add]; ring
  have hcast : (q.num.natAbs : ℚ) < (2 : ℚ)^(integerBits + precisionBits budget hbudget + 1) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hnum
  have hn : q.num.natAbs < 2^(integerBits + precisionBits budget hbudget + 1) := by exact_mod_cast hcast
  have hh := unsignedBitLength_le_of_lt_pow hn
  change Maxwell.unsignedBitLength q.num.natAbs + 1 ≤ _
  omega

theorem selectedRound_reduced_denominatorBits (budget : ℚ) (hbudget : 0 < budget) (x : ℚ) :
    Maxwell.unsignedBitLength (selectedRound budget hbudget x).value.den ≤
      precisionBits budget hbudget + 1 := by
  apply unsignedBitLength_le_of_lt_pow
  calc
    _ ≤ 2 ^ precisionBits budget hbudget := selectedRound_reduced_den_le budget hbudget x
    _ < 2 ^ (precisionBits budget hbudget + 1) := by
      rw [pow_succ]
      have h : 0 < 2 ^ precisionBits budget hbudget := by positivity
      omega

/-- Literal size bound for the canonical rational serialized by the encoder. -/
theorem selectedRound_rationalBitLength (budget : ℚ) (hbudget : 0 < budget)
    (x : ℚ) (integerBits : ℕ) (hx : |x| ≤ (2 : ℚ)^integerBits) :
    Maxwell.rationalBitLength (selectedRound budget hbudget x).value ≤
      integerBits + 2 * precisionBits budget hbudget + 3 := by
  have hn := selectedRound_reduced_numeratorBits budget hbudget x integerBits hx
  have hd := selectedRound_reduced_denominatorBits budget hbudget x
  unfold Maxwell.rationalBitLength
  omega

/-- The rounded sampled field satisfies the decoder's actual finite-word
range contract when the source samples obey the declared integer bound. -/
theorem selectedRound_fits {ι : Type*} {n : ℕ}
    (D : Maxwell.Target.WeightedDecoder ι n) (budget : ℚ) (hbudget : 0 < budget)
    (x : ι → ℚ) (integerBits : ℕ)
    (hformat : D.format = ⟨integerBits + 1, precisionBits budget hbudget⟩)
    (hx : ∀ j, |x (D.coordinate j)| ≤ (2 : ℚ)^integerBits) :
    D.Fits (fun i => ((selectedRound budget hbudget (x i)).value : ℝ)) := by
  intro j
  rw [hformat]
  exact selectedRound_inRange budget hbudget (x (D.coordinate j)) integerBits (hx j)

end Maxwell.Realization
