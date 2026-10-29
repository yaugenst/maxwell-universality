import Maxwell.Cost.Arithmetic

namespace Maxwell.Cost

/-- Binary Horner multiplication; the least significant bit is at the
front, so the recursive tail is processed before the current bit. This
recurrence is implemented using shift, ripple-add, rewind and tape-copy
blocks; no integer multiplication is assumed as a bit-machine primitive. -/
def multiplyBits (xs : List Bool) : List Bool → List Bool
  | [] => []
  | b :: ys =>
      let doubled := false :: multiplyBits xs ys
      if b then addBits false doubled xs else doubled

theorem multiplyBits_value (xs ys : List Bool) :
    addressValue (multiplyBits xs ys) = addressValue xs * addressValue ys := by
  induction ys with
  | nil => simp [multiplyBits, addressValue]
  | cons b ys ih =>
    cases b <;> simp [multiplyBits, addressValue, addBits_value, ih] <;> ring

/-- A deliberately permissive bound that remains valid for padded binary
words; it bounds actual allocated width without a canonicalization oracle. -/
theorem multiplyBits_length_le (xs ys : List Bool) :
    (multiplyBits xs ys).length ≤ xs.length + 2 * ys.length := by
  induction ys with
  | nil => simp [multiplyBits]
  | cons b ys ih =>
    have ha := addBits_length_le false (false :: multiplyBits xs ys) xs
    cases b <;> simp only [multiplyBits, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, Nat.mul_add, Nat.mul_one] at * <;> omega

/-- One Horner transition, with the accumulator made explicit for loop
invariants and nonzero initial words. -/
def multiplyStep (xs accumulator : List Bool) (b : Bool) : List Bool :=
  if b then addBits false (false :: accumulator) xs else false :: accumulator

def multiplyFrom (xs accumulator ys : List Bool) : List Bool :=
  ys.foldr (fun b acc => multiplyStep xs acc b) accumulator

@[simp] theorem multiplyFrom_nil (xs accumulator : List Bool) :
    multiplyFrom xs accumulator [] = accumulator := rfl

theorem multiplyFrom_append_bit (xs accumulator ys : List Bool) (b : Bool) :
    multiplyFrom xs accumulator (ys ++ [b]) =
      multiplyFrom xs (multiplyStep xs accumulator b) ys := by
  simp [multiplyFrom, List.foldr_append]

theorem multiplyFrom_empty (xs ys : List Bool) : multiplyFrom xs [] ys = multiplyBits xs ys := by
  induction ys with
  | nil => rfl
  | cons b ys ih => simp [multiplyFrom, multiplyStep, multiplyBits] at ih ⊢; rw [ih]

theorem multiplyStep_value (xs accumulator : List Bool) (b : Bool) :
    addressValue (multiplyStep xs accumulator b) =
      2 * addressValue accumulator + b.toNat * addressValue xs := by
  cases b <;> simp [multiplyStep, addBits_value, addressValue]

theorem multiplyStep_length_le (xs accumulator : List Bool) (b : Bool) (B : ℕ)
    (hx : xs.length ≤ B) (ha : accumulator.length ≤ B) :
    (multiplyStep xs accumulator b).length ≤ B + 2 := by
  have hh := addBits_length_le false (false :: accumulator) xs
  cases b <;> simp [multiplyStep] <;> simp only [List.length_cons] at hh <;> omega

theorem multiplyFrom_value (xs accumulator ys : List Bool) :
    addressValue (multiplyFrom xs accumulator ys) =
      2 ^ ys.length * addressValue accumulator + addressValue xs * addressValue ys := by
  induction ys with
  | nil => simp [multiplyFrom, addressValue]
  | cons b ys ih =>
    change addressValue (multiplyStep xs (multiplyFrom xs accumulator ys) b) = _
    rw [multiplyStep_value, ih]
    simp only [List.length_cons, pow_succ, addressValue]
    ring

/-- An explicit cost recurrence for the Horner calls. The constant covers
charged shifts, branch tests, linked calls, clearing, copying and rewinds.
The concrete machine proof must discharge this recurrence, rather than
assigning it as arbitrary metadata. -/
def multiplyCostEnvelope (xwidth : ℕ) : ℕ → ℕ
  | 0 => 16
  | n + 1 => multiplyCostEnvelope xwidth n + 200 * (xwidth + 2 * n + 4)

theorem multiplyCostEnvelope_le (xwidth width : ℕ) :
    multiplyCostEnvelope xwidth width ≤ 400 * (xwidth + width + 1) * (width + 1) := by
  induction width with
  | zero => simp [multiplyCostEnvelope]; omega
  | succ width ih =>
    rw [multiplyCostEnvelope]
    nlinarith

end Maxwell.Cost
