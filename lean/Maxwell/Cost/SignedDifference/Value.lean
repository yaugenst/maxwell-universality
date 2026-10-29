import Maxwell.Cost.SignedDifference.Pad

namespace Maxwell.Cost.SignedDifference

def sign (xs ys : List Bool) : Bool := (Subtraction.result false (padded xs) (padded ys)).2

def magnitude (xs ys : List Bool) : List Bool :=
  if sign xs ys then (Subtraction.result false (padded ys) (padded xs)).1
  else (Subtraction.result false (padded xs) (padded ys)).1

theorem sign_iff (xs ys : List Bool) :
    sign xs ys = true ↔ addressValue xs < addressValue ys := by
  simpa [sign] using Subtraction.final_borrow_iff (padded xs) (padded ys)

theorem reverse_borrow_false (xs ys : List Bool) (h : sign xs ys = true) :
    (Subtraction.result false (padded ys) (padded xs)).2 = false := by
  have hh := (sign_iff xs ys).mp h
  have hr := Subtraction.final_borrow_iff (padded ys) (padded xs)
  simp only [padded_value] at hr
  cases hb : (Subtraction.result false (padded ys) (padded xs)).2 <;> simp_all
  all_goals omega

theorem magnitude_length (xs ys : List Bool) :
    (magnitude xs ys).length = max (padded xs).length (padded ys).length := by
  unfold magnitude
  split_ifs <;> simp [Subtraction.result_length, max_comm]

theorem magnitude_length_le (xs ys : List Bool) :
    (magnitude xs ys).length ≤ max xs.length ys.length + 1 := by
  rw [magnitude_length]
  have hx := padded_length xs
  have hy := padded_length ys
  omega

theorem signed_value (xs ys : List Bool) :
    (if sign xs ys then -(addressValue (magnitude xs ys) : ℤ)
      else (addressValue (magnitude xs ys) : ℤ)) =
      (addressValue xs : ℤ) - (addressValue ys : ℤ) := by
  cases hb : sign xs ys with
  | false =>
    have hv := Subtraction.result_value false (padded xs) (padded ys)
    change (Subtraction.result false (padded xs) (padded ys)).2 = false at hb
    simp only [hb, Bool.toNat_false, mul_zero, add_zero, padded_value] at hv
    have hi := congrArg (fun n : ℕ => (n : ℤ)) hv
    push_cast at hi
    simp only [magnitude, sign, hb, Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    have hr := reverse_borrow_false xs ys hb
    have hv := Subtraction.result_value false (padded ys) (padded xs)
    simp only [hr, Bool.toNat_false, mul_zero, add_zero, padded_value] at hv
    have hi := congrArg (fun n : ℕ => (n : ℤ)) hv
    push_cast at hi
    simp only [magnitude, hb, ↓reduceIte]
    omega

theorem zero_sign (xs ys : List Bool) (h : addressValue (magnitude xs ys) = 0) :
    sign xs ys = false := by
  have hv := signed_value xs ys
  have hs := sign_iff xs ys
  rw [h] at hv
  cases hb : sign xs ys <;> simp_all
  all_goals omega

end Maxwell.Cost.SignedDifference
