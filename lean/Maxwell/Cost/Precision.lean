import Maxwell.Cost.Model
import Maxwell.Interfaces

set_option linter.unusedSimpArgs false

namespace Maxwell.Cost

/-- Arithmetic bisection uses only addition, multiplication by one half,
and comparison. It does not assume a floor instruction on a real input. -/
noncomputable def bisect (x : ℝ) : ℕ → ℝ → ℝ → Program (ℝ × ℝ)
  | 0, lower, upper => pure (lower, upper)
  | n + 1, lower, upper => do
      let sum : ℝ ← perform (.add lower upper)
      let middle : ℝ ← perform (.multiply sum (1 / 2))
      let left : Bool ← perform (.compare x middle)
      if left = true then bisect x n lower middle else bisect x n middle upper

@[simp] theorem bisect_zero (x lower upper : ℝ) :
    (bisect x 0 lower upper).result = (lower, upper) := rfl

@[simp] theorem bisect_succ (x lower upper : ℝ) (n : ℕ) :
    (bisect x (n + 1) lower upper).result =
      if x ≤ (lower + upper) / 2 then
        (bisect x n lower ((lower + upper) / 2)).result
      else (bisect x n ((lower + upper) / 2) upper).result := by
  rw [bisect]
  simp only [bind, Program.bind, perform, Program.result, Instruction.execute]
  simp only [decide_eq_true_eq, div_eq_mul_inv, one_mul]
  split_ifs <;> rfl

/-- Exactly three arithmetic/comparison operations per fractional bit. -/
theorem bisect_steps (x lower upper : ℝ) (n : ℕ) :
    (bisect x n lower upper).steps = 3 * n := by
  induction n generalizing lower upper with
  | zero => rfl
  | succ n ih =>
    rw [bisect]
    simp only [bind, steps_bind, steps_perform]
    have hb : ∀ (middle : ℝ) (left : Bool),
        (if left = true then bisect x n lower middle else bisect x n middle upper).steps = 3 * n := by
      intro middle left
      cases left <;> simp [ih]
    rw [hb]
    simp only [perform, Program.steps, steps_halt]
    omega

/-- All bisection steps preserve the enclosure and halve its width. -/
theorem bisect_enclosure (x lower upper : ℝ) (n : ℕ)
    (hlo : lower ≤ x) (hhi : x ≤ upper) :
    let interval := (bisect x n lower upper).result
    interval.1 ≤ x ∧ x ≤ interval.2 ∧
      interval.2 - interval.1 = (upper - lower) / 2 ^ n := by
  induction n generalizing lower upper with
  | zero => simp [bisect]; exact ⟨hlo, hhi, rfl⟩
  | succ n ih =>
    rw [bisect_succ]
    split_ifs with h
    · have hmiddle : lower ≤ (lower + upper) / 2 := by linarith
      have hr := ih lower ((lower + upper) / 2) hlo h
      refine ⟨hr.1, hr.2.1, ?_⟩
      rw [hr.2.2, pow_succ]
      ring
    · have hmiddle : (lower + upper) / 2 ≤ x := le_of_lt (lt_of_not_ge h)
      have hr := ih ((lower + upper) / 2) upper hmiddle hhi
      refine ⟨hr.1, hr.2.1, ?_⟩
      rw [hr.2.2, pow_succ]
      ring

/-- A real in [-1,1] is rounded to absolute error `2^-p` by `p+1`
bisections. The operation count is exactly `3*(p+1)`. -/
theorem bisect_unit_error (x : ℝ) (p : ℕ) (hlo : -1 ≤ x) (hhi : x ≤ 1) :
    |(bisect x (p + 1) (-1) 1).result.1 - x| ≤ ((2 : ℝ) ^ p)⁻¹ := by
  have h := bisect_enclosure x (-1) 1 (p + 1) hlo hhi
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h.1)]
  calc
    x - (bisect x (p + 1) (-1) 1).result.1 ≤
        (bisect x (p + 1) (-1) 1).result.2 -
          (bisect x (p + 1) (-1) 1).result.1 := sub_le_sub_right h.2.1 _
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [h.2.2, pow_succ]; ring

/-- Bisection never leaves its initial interval, even when `x` lies outside. -/
theorem bisect_subinterval (x lower upper : ℝ) (n : ℕ) (h : lower ≤ upper) :
    lower ≤ (bisect x n lower upper).result.1 ∧
      (bisect x n lower upper).result.2 ≤ upper := by
  induction n generalizing lower upper with
  | zero => simp
  | succ n ih =>
    rw [bisect_succ]
    split_ifs
    · have hm : lower ≤ (lower + upper) / 2 := by linarith
      have hr := ih lower ((lower + upper) / 2) hm
      exact ⟨hr.1, by linarith [hr.2]⟩
    · have hm : (lower + upper) / 2 ≤ upper := by linarith
      have hr := ih ((lower + upper) / 2) upper hm
      exact ⟨by linarith [hr.1], hr.2⟩

/-- Every endpoint is a genuine dyadic, obtained by the actual bisection
recursion. No floor or real-to-integer conversion is postulated. -/
theorem bisect_dyadic (x : ℝ) (n p : ℕ) (a b : ℤ) :
    ∃ c d : ℤ, (bisect x n ((a : ℝ) / 2 ^ p) ((b : ℝ) / 2 ^ p)).result =
      ((c : ℝ) / 2 ^ (p + n), (d : ℝ) / 2 ^ (p + n)) := by
  induction n generalizing p a b with
  | zero => exact ⟨a, b, by simp⟩
  | succ n ih =>
    rw [bisect_succ]
    have ha : (a : ℝ) / 2 ^ p = ((2 * a : ℤ) : ℝ) / 2 ^ (p + 1) := by
      push_cast
      rw [pow_succ]
      ring
    have hb : (b : ℝ) / 2 ^ p = ((2 * b : ℤ) : ℝ) / 2 ^ (p + 1) := by
      push_cast
      rw [pow_succ]
      ring
    have hm : ((a : ℝ) / 2 ^ p + (b : ℝ) / 2 ^ p) / 2 =
        ((a + b : ℤ) : ℝ) / 2 ^ (p + 1) := by
      push_cast
      rw [pow_succ]
      ring
    split_ifs
    · rw [hm, ha]
      obtain ⟨c, d, hcd⟩ := ih (p + 1) (2 * a) (a + b)
      exact ⟨c, d, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcd⟩
    · rw [hm, hb]
      obtain ⟨c, d, hcd⟩ := ih (p + 1) (a + b) (2 * b)
      exact ⟨c, d, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcd⟩

/-- A representation with a bounded numerator has explicitly bounded
magnitude and denominator fields. This bound is independent of reducing
fractions to lowest terms. -/
def BoundedDyadic (integerBits fractionalBits : ℕ) :=
  {d : Maxwell.Dyadic fractionalBits // d.numerator.natAbs < 2 ^ (integerBits + fractionalBits)}

theorem unsignedBitLength_le_of_lt_pow {n bits : ℕ} (h : n < 2 ^ bits) :
    Maxwell.unsignedBitLength n ≤ bits := by
  by_cases hn : n = 0
  · simp [Maxwell.unsignedBitLength, hn]
  · have hlog : n.log2 < bits := (Nat.log2_lt hn).mpr h
    simp only [Maxwell.unsignedBitLength, hn, ite_false]
    omega

theorem boundedDyadic_numerator_bits (integerBits fractionalBits : ℕ)
    (d : BoundedDyadic integerBits fractionalBits) :
    d.val.numeratorBits ≤ integerBits + fractionalBits + 1 := by
  have h := unsignedBitLength_le_of_lt_pow d.property
  exact Nat.add_le_add_right h 1

/-- The actual bounded-input rounding has a short signed numerator, not
just an abstract fixed-point format with an assumed size bound. -/
theorem bisect_unit_short_numerator (x : ℝ) (p : ℕ)
    (hlo : -1 ≤ x) (hhi : x ≤ 1) :
    ∃ a : ℤ, (bisect x (p + 1) (-1) 1).result.1 = (a : ℝ) / 2 ^ (p + 1) ∧
      Maxwell.signedBitLength a ≤ p + 3 := by
  obtain ⟨a, b, hab⟩ := bisect_dyadic x (p + 1) 0 (-1) 1
  simp only [pow_zero, div_one, Int.cast_neg, Int.cast_one, zero_add] at hab
  have ha : (bisect x (p + 1) (-1) 1).result.1 = (a : ℝ) / 2 ^ (p + 1) :=
    congrArg Prod.fst hab
  have hinterval := bisect_subinterval x (-1) 1 (p + 1) (by norm_num)
  have henclose := bisect_enclosure x (-1) 1 (p + 1) hlo hhi
  have hden : (0 : ℝ) < 2 ^ (p + 1) := by positivity
  have hl : -(2 : ℝ) ^ (p + 1) ≤ (a : ℝ) := by
    have hh := hinterval.1
    rw [ha] at hh
    have hh' := (le_div_iff₀ hden).mp hh
    nlinarith
  have hu : (a : ℝ) ≤ (2 : ℝ) ^ (p + 1) := by
    have hh := henclose.1.trans hhi
    rw [ha] at hh
    simpa using (div_le_iff₀ hden).mp hh
  have hnat : a.natAbs ≤ 2 ^ (p + 1) := by
    have habs : |(a : ℝ)| ≤ (2 : ℝ) ^ (p + 1) := abs_le.mpr ⟨hl, hu⟩
    have hi : |a| ≤ ((2 ^ (p + 1) : ℕ) : ℤ) := by exact_mod_cast habs
    simpa only [Int.abs_eq_natAbs, Int.ofNat_le] using hi
  have hstrict : a.natAbs < 2 ^ (p + 2) := by
    have hp : 0 < 2 ^ (p + 1) := Nat.pow_pos (by omega)
    have heq : 2 ^ (p + 2) = 2 ^ (p + 1) * 2 := by rw [show p + 2 = (p + 1) + 1 by omega, pow_succ]
    rw [heq]
    omega
  refine ⟨a, ha, ?_⟩
  have hbits := unsignedBitLength_le_of_lt_pow hstrict
  unfold Maxwell.signedBitLength
  omega

/-- The denominator field is exactly the fractional precision plus one. -/
theorem boundedDyadic_denominator_bits (integerBits fractionalBits : ℕ)
    (_d : BoundedDyadic integerBits fractionalBits) :
    Maxwell.unsignedBitLength (2 ^ fractionalBits) = fractionalBits + 1 :=
  Maxwell.Dyadic.denominator_bitLength fractionalBits

/-- Uniform fixed-point output writes every supplied representation bit. -/
def emitDyadicBits (sign : Bool) (integer fractional : List Bool) : Program Unit :=
  writeBits (sign :: integer ++ fractional)

theorem emitDyadicBits_steps (sign : Bool) (integer fractional : List Bool) :
    (emitDyadicBits sign integer fractional).steps =
      1 + integer.length + fractional.length := by
  simp [emitDyadicBits, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end Maxwell.Cost
