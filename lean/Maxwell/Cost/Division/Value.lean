import Maxwell.Cost.Subtraction

namespace Maxwell.Cost.Division

/-- The subtractor's actual final borrow selects the next remainder. -/
def remainderStep (divisor remainder : List Bool) (b : Bool) : List Bool :=
  let sub := Subtraction.result false (b :: remainder) divisor
  if sub.2 then b :: remainder else sub.1

def quotientBit (divisor remainder : List Bool) (b : Bool) : Bool :=
  !(Subtraction.result false (b :: remainder) divisor).2

def step (divisor : List Bool) (state : List Bool × List Bool) (b : Bool) :
    List Bool × List Bool :=
  (remainderStep divisor state.1 b, quotientBit divisor state.1 b :: state.2)

def divideFrom (divisor remainder quotient remaining : List Bool) : List Bool × List Bool :=
  remaining.foldr (fun b state => step divisor state b) (remainder, quotient)

@[simp] theorem divideFrom_nil (divisor remainder quotient : List Bool) :
    divideFrom divisor remainder quotient [] = (remainder, quotient) := rfl

theorem divideFrom_append_bit (divisor remainder quotient remaining : List Bool) (b : Bool) :
    divideFrom divisor remainder quotient (remaining ++ [b]) =
      divideFrom divisor (remainderStep divisor remainder b)
        (quotientBit divisor remainder b :: quotient) remaining := by
  simp [divideFrom, List.foldr_append, step]

theorem step_value (divisor remainder quotient : List Bool) (b : Bool)
    (_hd : 0 < addressValue divisor) (hr : addressValue remainder < addressValue divisor) :
    addressValue (remainderStep divisor remainder b) < addressValue divisor ∧
      addressValue divisor * addressValue (quotientBit divisor remainder b :: quotient) +
        addressValue (remainderStep divisor remainder b) =
      2 * (addressValue divisor * addressValue quotient + addressValue remainder) + b.toNat := by
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have hv := Subtraction.result_value false (b :: remainder) divisor
  have hborrow := Subtraction.final_borrow_iff (b :: remainder) divisor
  cases hs : (Subtraction.result false (b :: remainder) divisor).2 <;>
    simp only [hs, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero,
      addressValue] at hv hborrow
  · simp only [remainderStep, quotientBit, hs, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, addressValue, Bool.toNat_true]
    constructor <;> nlinarith
  · simp only [remainderStep, quotientBit, hs, ↓reduceIte, Bool.not_true,
      addressValue, Bool.toNat_false]
    constructor
    · exact hborrow.mp trivial
    · ring

theorem remainderStep_length_le (divisor remainder : List Bool) (b : Bool) (B : ℕ)
    (hd : divisor.length ≤ B) (hr : remainder.length ≤ B) :
    (remainderStep divisor remainder b).length ≤ B + 1 := by
  dsimp only [remainderStep]
  split
  · simp only [List.length_cons]; omega
  · rw [Subtraction.result_length]
    simp only [List.length_cons]
    omega

theorem divideFrom_value (divisor remainder quotient remaining : List Bool)
    (hd : 0 < addressValue divisor) (hr : addressValue remainder < addressValue divisor) :
    addressValue (divideFrom divisor remainder quotient remaining).1 < addressValue divisor ∧
      addressValue divisor * addressValue (divideFrom divisor remainder quotient remaining).2 +
        addressValue (divideFrom divisor remainder quotient remaining).1 =
      2 ^ remaining.length * (addressValue divisor * addressValue quotient + addressValue remainder) +
        addressValue remaining := by
  induction remaining with
  | nil => simpa [divideFrom, addressValue] using hr
  | cons b remaining ih =>
      have hs := step_value divisor (divideFrom divisor remainder quotient remaining).1
        (divideFrom divisor remainder quotient remaining).2 b hd ih.1
      change addressValue (step divisor (divideFrom divisor remainder quotient remaining) b).1 < _ ∧ _
      refine ⟨hs.1, ?_⟩
      change addressValue divisor * addressValue
        (quotientBit divisor (divideFrom divisor remainder quotient remaining).1 b ::
          (divideFrom divisor remainder quotient remaining).2) +
        addressValue (remainderStep divisor (divideFrom divisor remainder quotient remaining).1 b) = _
      rw [hs.2, ih.2]
      simp only [List.length_cons, pow_succ, addressValue]
      ring

theorem divideFrom_length_le (divisor remainder quotient remaining : List Bool) (B : ℕ)
    (hd : divisor.length ≤ B) (hr : remainder.length ≤ B) :
    (divideFrom divisor remainder quotient remaining).1.length ≤ B + remaining.length ∧
    (divideFrom divisor remainder quotient remaining).2.length = quotient.length + remaining.length := by
  induction remaining with
  | nil => simpa [divideFrom] using hr
  | cons b remaining ih =>
      have hl := remainderStep_length_le divisor
        (divideFrom divisor remainder quotient remaining).1 b (B + remaining.length)
        (by omega) ih.1
      change (remainderStep divisor (divideFrom divisor remainder quotient remaining).1 b).length ≤ _ ∧ _
      constructor
      · simpa only [List.length_cons, Nat.add_assoc] using hl
      · change (quotientBit divisor (divideFrom divisor remainder quotient remaining).1 b ::
          (divideFrom divisor remainder quotient remaining).2).length = _
        simp [ih.2, Nat.add_assoc]

end Maxwell.Cost.Division
