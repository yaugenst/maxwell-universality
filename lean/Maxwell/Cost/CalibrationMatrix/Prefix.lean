import Maxwell.Cost.CalibrationMatrix.Data
import Mathlib.Algebra.BigOperators.Fin

namespace Maxwell.Cost.CalibrationMatrix

open scoped BigOperators

def partialSum {n : ℕ} (f : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ j, if j.val < k then f j else 0

@[simp] theorem partialSum_zero {n : ℕ} (f : Fin n → ℕ) : partialSum f 0 = 0 := by simp [partialSum]

@[simp] theorem partialSum_full {n : ℕ} (f : Fin n → ℕ) : partialSum f n = ∑ j, f j := by
  simp [partialSum]

theorem partialSum_succ {n : ℕ} (f : Fin n → ℕ) (k : ℕ) (hk : k < n) :
    partialSum f (k+1) = partialSum f k + f ⟨k,hk⟩ := by
  have he (j : Fin n) : (if j.val < k+1 then f j else 0) =
      (if j.val < k then f j else 0) + (if j = ⟨k,hk⟩ then f j else 0) := by
    by_cases hlt : j.val < k
    · have hne : j ≠ ⟨k,hk⟩ := by
        intro h
        have heq : j.val = k := congrArg Fin.val h
        omega
      simp [hlt, hne, show j.val < k+1 by omega]
    · by_cases heq : j = ⟨k,hk⟩
      · subst j; simp
      · have hn : ¬j.val < k+1 := by
          intro h
          apply heq
          apply Fin.ext
          change j.val = k
          omega
        simp [hlt, heq, hn]
  simp only [partialSum, he, Finset.sum_add_distrib]
  simp

theorem partialSum_le_full {n : ℕ} (f : Fin n → ℕ) (k : ℕ) : partialSum f k ≤ ∑ j, f j := by
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> omega

theorem partialSum_bits_le {n : ℕ} (f : Fin n → ℕ) (k B : ℕ)
    (h : (∑ j, f j).bits.length ≤ B) : (partialSum f k).bits.length ≤ B := by
  rw [Nat.size_eq_bits_len] at h ⊢
  exact (Nat.size_le_size (partialSum_le_full f k)).trans h

def rowIndex {m n : ℕ} (start : ℕ) (h : start+n ≤ m) (j : Fin n) : Fin m :=
  ⟨start+j.val, by omega⟩

def Data.rowPositive {m n : ℕ} (d : Data m n) (start : ℕ) (h : start+n ≤ m) : Fin n → ℕ :=
  fun j => d.positiveTerm (rowIndex start h j) j

def Data.rowNegative {m n : ℕ} (d : Data m n) (start : ℕ) (h : start+n ≤ m) : Fin n → ℕ :=
  fun j => d.negativeTerm (rowIndex start h j) j

end Maxwell.Cost.CalibrationMatrix
