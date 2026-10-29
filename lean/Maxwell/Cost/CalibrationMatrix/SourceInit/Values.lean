import Maxwell.Cost.CalibrationMatrix.Prefix
import Maxwell.Cost.CalibrationMatrix.Value

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

open scoped BigOperators

/-- Logical values decoded from three sparse input arrays. Repeated target
indices are retained and accumulated in their original order. -/
structure Records (m n : ℕ) where
  index : Fin m → Fin n
  positive : Fin m → ℕ
  negative : Fin m → ℕ

def values {m n : ℕ} (r : Records m n) (k : ℕ) : Channels n where
  positive i := partialSum (fun j => if r.index j = i then r.positive j else 0) k
  negative i := partialSum (fun j => if r.index j = i then r.negative j else 0) k

@[simp] theorem values_zero_positive {m n : ℕ} (r : Records m n) (i : Fin n) :
    (values r 0).positive i = 0 := by simp [values]

@[simp] theorem values_zero_negative {m n : ℕ} (r : Records m n) (i : Fin n) :
    (values r 0).negative i = 0 := by simp [values]

theorem values_step_positive {m n : ℕ} (r : Records m n) (j : Fin m) :
    (values r (j.val+1)).positive = Function.update (values r j.val).positive (r.index j)
      ((values r j.val).positive (r.index j)+r.positive j) := by
  funext i
  change partialSum (fun k => if r.index k = i then r.positive k else 0) (j.val+1) = _
  rw [partialSum_succ _ _ j.isLt]
  change (values r j.val).positive i + (if r.index j = i then r.positive j else 0) = _
  by_cases h : i = r.index j
  · subst i; simp
  · simp [h, Ne.symm h]

theorem values_step_negative {m n : ℕ} (r : Records m n) (j : Fin m) :
    (values r (j.val+1)).negative = Function.update (values r j.val).negative (r.index j)
      ((values r j.val).negative (r.index j)+r.negative j) := by
  funext i
  change partialSum (fun k => if r.index k = i then r.negative k else 0) (j.val+1) = _
  rw [partialSum_succ _ _ j.isLt]
  change (values r j.val).negative i + (if r.index j = i then r.negative j else 0) = _
  by_cases h : i = r.index j
  · subst i; simp
  · simp [h, Ne.symm h]

theorem values_positive_le {m n : ℕ} (r : Records m n) (k : ℕ) (i : Fin n) :
    (values r k).positive i ≤ ∑ j, r.positive j := by
  apply (partialSum_le_full _ k).trans
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> omega

theorem values_negative_le {m n : ℕ} (r : Records m n) (k : ℕ) (i : Fin n) :
    (values r k).negative i ≤ ∑ j, r.negative j := by
  apply (partialSum_le_full _ k).trans
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> omega

theorem values_positive_bits_le {m n : ℕ} (r : Records m n) (k B : ℕ)
    (h : (∑ j, r.positive j).bits.length ≤ B) (i : Fin n) :
    ((values r k).positive i).bits.length ≤ B := by
  rw [Nat.size_eq_bits_len] at h ⊢
  exact (Nat.size_le_size (values_positive_le r k i)).trans h

theorem values_negative_bits_le {m n : ℕ} (r : Records m n) (k B : ℕ)
    (h : (∑ j, r.negative j).bits.length ≤ B) (i : Fin n) :
    ((values r k).negative i).bits.length ≤ B := by
  rw [Nat.size_eq_bits_len] at h ⊢
  exact (Nat.size_le_size (values_negative_le r k i)).trans h

/-- The output represents the sum of all signed records at each index;
positive and negative channels need not be canonical after cancellation. -/
theorem values_full {m n : ℕ} (r : Records m n) (i : Fin n) :
    (values r m).value i = ∑ j, if r.index j = i then
      ((r.positive j : ℤ)-r.negative j) else 0 := by
  simp only [Channels.value, values, partialSum_full, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

end Maxwell.Cost.CalibrationMatrix.SourceInit
