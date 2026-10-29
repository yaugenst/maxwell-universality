import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Exact recursion-tree budgets for the materialized pointer-doubling
implementation of binary incidence coloring. Each internal node has two
half-degree children. This module bounds the stated sixteen-operation split
budget; the machine-cost bridge must separately charge permutation and output
materialization before identifying it with complete compiler execution.
The leaf budget includes writing its constant color array. -/

namespace Maxwell.Logical.Routing.ColoringCounts

/-- Primitive-operation budget for one actual stored-array split. -/
def splitBudget (tokens : ℕ) : ℕ := 16 * tokens * (Nat.clog 2 tokens + 1)

/-- The work recurrence follows the two recursive color-fiber calls.  Rows
remain fixed and degree is halved at each child. -/
def work : ℕ → ℕ → ℕ
  | 0, rows => 16 * rows
  | depth + 1, rows =>
      2 * work depth rows + splitBudget (2 ^ (depth + 1) * rows)

@[simp] theorem work_zero (rows : ℕ) : work 0 rows = 16 * rows := rfl

@[simp] theorem work_succ (depth rows : ℕ) :
    work (depth + 1) rows =
      2 * work depth rows + splitBudget (2 ^ (depth + 1) * rows) := rfl

/-- Binary degree and row counts make the number of doubling passes exact. -/
theorem rounds_power_two (depth rowsExponent : ℕ) :
    Nat.clog 2 (2 ^ depth * 2 ^ rowsExponent) = depth + rowsExponent := by
  rw [← pow_add, Nat.clog_pow _ _ (by omega)]

/-- A bound for every depth and every power-of-two row count, before setting
the row count equal to the original degree. -/
theorem work_power_two_le (depth rowsExponent : ℕ) :
    work depth (2 ^ rowsExponent) ≤
      16 * (2 ^ depth * 2 ^ rowsExponent) *
        (1 + depth * (depth + rowsExponent + 1)) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
    rw [work_succ, splitBudget, rounds_power_two, pow_succ]
    calc
      2 * work depth (2 ^ rowsExponent) +
          16 * (2 ^ depth * 2 * 2 ^ rowsExponent) * (depth + 1 + rowsExponent + 1)
          ≤ 2 * (16 * (2 ^ depth * 2 ^ rowsExponent) *
              (1 + depth * (depth + rowsExponent + 1))) +
            16 * (2 ^ depth * 2 * 2 ^ rowsExponent) *
              (depth + 1 + rowsExponent + 1) := by omega
      _ ≤ 16 * (2 ^ depth * 2 * 2 ^ rowsExponent) *
          (1 + (depth + 1) * (depth + 1 + rowsExponent + 1)) := by
        nlinarith [Nat.zero_le
          (32 * 2 ^ depth * 2 ^ rowsExponent * depth)]

/-- The logarithmic factor is uniformly absorbed by one further side length,
including the smallest grids. -/
theorem quadratic_le_three_pow (depth : ℕ) :
    1 + 2 * depth ^ 2 + depth ≤ 3 * 2 ^ depth := by
  induction depth with
  | zero => norm_num
  | succ depth ih =>
    by_cases hsmall : depth < 2
    · interval_cases depth <;> norm_num
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ depth by omega)
      rw [pow_succ (2 : ℕ) (2 + k)]
      nlinarith [Nat.zero_le (k * k)]

/-- The stated binary-splitting budget is at most 48 q³ when both the original
degree and row count are q = 2^depth. -/
theorem work_square_le_cubic (depth : ℕ) :
    work depth (2 ^ depth) ≤ 48 * (2 ^ depth) ^ 3 := by
  have hwork := work_power_two_le depth depth
  have hquad := quadratic_le_three_pow depth
  calc
    work depth (2 ^ depth)
        ≤ 16 * (2 ^ depth * 2 ^ depth) * (1 + 2 * depth ^ 2 + depth) := by
          convert hwork using 1
          ring
    _ ≤ 16 * (2 ^ depth * 2 ^ depth) * (3 * 2 ^ depth) := by
      exact Nat.mul_le_mul_left _ hquad
    _ = 48 * (2 ^ depth) ^ 3 := by ring

end Maxwell.Logical.Routing.ColoringCounts
