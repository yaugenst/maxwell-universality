import Maxwell.Logical.Rounding

namespace Maxwell.Cost.SignedRound

def increment (negative : Bool) (numerator denominator : ℕ) : ℕ :=
  if negative then if denominator < 2*(numerator % denominator) then 1 else 0
  else if denominator ≤ 2*(numerator % denominator) then 1 else 0

def magnitude (negative : Bool) (numerator denominator : ℕ) : ℕ :=
  numerator / denominator + increment negative numerator denominator

def rounded (negative : Bool) (numerator denominator : ℕ) : ℤ :=
  if negative then -(magnitude negative numerator denominator : ℤ)
  else magnitude negative numerator denominator

/-- Exact signed half-up rounding by one unsigned division and a remainder
comparison. The strict inequality on the negative branch is essential at ties. -/
theorem rounded_eq_floor (negative : Bool) (numerator denominator : ℕ)
    (hd : 0 < denominator) :
    rounded negative numerator denominator =
      ⌊(if negative then -(numerator : ℚ) else numerator) / denominator + 1/2⌋ := by
  have hdq : (0 : ℚ) < denominator := by exact_mod_cast hd
  have hremainder : numerator % denominator < denominator := Nat.mod_lt _ hd
  have he : numerator = numerator / denominator * denominator + numerator % denominator := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod numerator denominator).symm
  have heq := congrArg (fun n : ℕ => (n : ℚ)) he
  push_cast at heq
  have hrq : ((numerator % denominator : ℕ) : ℚ) < denominator := by exact_mod_cast hremainder
  have hr0 : (0 : ℚ) ≤ ((numerator % denominator : ℕ) : ℚ) := by positivity
  have hfrac0 : (0 : ℚ) ≤ ((numerator % denominator : ℕ) : ℚ) / denominator := div_nonneg hr0 hdq.le
  have hfrac1 : ((numerator % denominator : ℕ) : ℚ) / denominator < 1 :=
    (div_lt_one hdq).mpr hrq
  have hdiv : (numerator : ℚ) / denominator =
      (numerator / denominator : ℕ) + ((numerator % denominator : ℕ) : ℚ) / denominator := by
    apply (div_eq_iff hdq.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hdq.ne']
    exact heq
  symm
  rw [Int.floor_eq_iff]
  cases negative
  · simp only [rounded, magnitude, increment, Bool.false_eq_true, ↓reduceIte]
    by_cases hc : denominator ≤ 2*(numerator % denominator)
    · have hcq : (denominator : ℚ) ≤ 2*((numerator % denominator : ℕ) : ℚ) := by exact_mod_cast hc
      simp only [hc, ↓reduceIte]
      simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one, Int.cast_natCast]
      have hhalf : (1/2 : ℚ) ≤ ((numerator % denominator : ℕ) : ℚ) / denominator :=
        (le_div_iff₀ hdq).mpr (by nlinarith)
      rw [hdiv]
      constructor <;> linarith
    · have hcq : 2*((numerator % denominator : ℕ) : ℚ) < denominator := by exact_mod_cast (Nat.lt_of_not_ge hc)
      simp only [hc, ↓reduceIte, Nat.add_zero, Int.cast_natCast]
      have hhalf : ((numerator % denominator : ℕ) : ℚ) / denominator < 1/2 :=
        (div_lt_iff₀ hdq).mpr (by nlinarith)
      rw [hdiv]
      constructor <;> linarith
  · simp only [rounded, magnitude, increment, ↓reduceIte]
    by_cases hc : denominator < 2*(numerator % denominator)
    · have hcq : (denominator : ℚ) < 2*((numerator % denominator : ℕ) : ℚ) := by exact_mod_cast hc
      simp only [hc, ↓reduceIte]
      simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_neg]
      have hhalf : (1/2 : ℚ) < ((numerator % denominator : ℕ) : ℚ) / denominator :=
        (lt_div_iff₀ hdq).mpr (by nlinarith)
      rw [neg_div, hdiv]
      constructor <;> linarith
    · have hcq : 2*((numerator % denominator : ℕ) : ℚ) ≤ denominator := by exact_mod_cast (Nat.le_of_not_gt hc)
      simp only [hc, ↓reduceIte, Nat.add_zero, Int.cast_neg, Int.cast_natCast]
      have hhalf : ((numerator % denominator : ℕ) : ℚ) / denominator ≤ 1/2 :=
        (div_le_iff₀ hdq).mpr (by nlinarith)
      rw [neg_div, hdiv]
      constructor <;> linarith

theorem rounded_dyadic (negative : Bool) (numerator denominator precision : ℕ)
    (hd : 0 < denominator) :
    rounded negative (numerator * 2^precision) denominator =
      (Logical.Rounding.nearest precision
        ((if negative then -(numerator : ℚ) else numerator) / denominator)).numerator := by
  rw [rounded_eq_floor negative _ _ hd]
  unfold Logical.Rounding.nearest
  congr 1
  cases negative <;> simp <;> ring

end Maxwell.Cost.SignedRound
