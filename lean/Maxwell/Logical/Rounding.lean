import Maxwell.Interfaces
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! Actual rational nearest-grid rounding and its uniform error contract.
The fixed half-up tie rule is explicit. No real floor oracle is used: the
encoder applies this function only to rational input values.
-/

namespace Maxwell.Logical.Rounding

def nearest (precision : ℕ) (q : ℚ) : Maxwell.Dyadic precision :=
  ⟨⌊q * (2 : ℚ) ^ precision + 1 / 2⌋⟩

theorem nearest_value (precision : ℕ) (q : ℚ) :
    (nearest precision q).value =
      (⌊q * (2 : ℚ) ^ precision + 1 / 2⌋ : ℚ) / (2 : ℚ) ^ precision := rfl

/-- The standard half-grid error, proved for all rational inputs and precisions. -/
theorem nearest_error (precision : ℕ) (q : ℚ) :
    |(nearest precision q).value - q| ≤ 1 / (2 * (2 : ℚ) ^ precision) := by
  have hp : (0 : ℚ) < 2 ^ precision := pow_pos (by norm_num) _
  have hlo := Int.floor_le (q * (2 : ℚ) ^ precision + 1 / 2)
  have hhi := Int.lt_floor_add_one (q * (2 : ℚ) ^ precision + 1 / 2)
  have hb : |(⌊q * (2 : ℚ) ^ precision + 1 / 2⌋ : ℚ) - q * 2 ^ precision| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  rw [nearest_value]
  calc
    |(⌊q * (2 : ℚ) ^ precision + 1 / 2⌋ : ℚ) / 2 ^ precision - q| =
        |(⌊q * (2 : ℚ) ^ precision + 1 / 2⌋ : ℚ) - q * 2 ^ precision| / 2 ^ precision := by
      have heq : (⌊q * (2 : ℚ) ^ precision + 1 / 2⌋ : ℚ) / 2 ^ precision - q =
          ((⌊q * (2 : ℚ) ^ precision + 1 / 2⌋ : ℚ) - q * 2 ^ precision) / 2 ^ precision := by
        field_simp
      rw [heq, abs_div, abs_of_pos hp]
    _ ≤ (1 / 2) / (2 : ℚ) ^ precision := div_le_div_of_nonneg_right hb hp.le
    _ = _ := by ring

@[simp] theorem nearest_zero (precision : ℕ) : (nearest precision 0).value = 0 := by
  simp [nearest, Maxwell.Dyadic.value]
  norm_num

def matrix {r c : Type*} (precision : ℕ) (A : Matrix r c ℚ) : Matrix r c ℚ :=
  fun i j => (nearest precision (A i j)).value

/-- Rounding can remove a stored nonzero but cannot create a new support entry. -/
theorem matrix_zero_preserved {r c : Type*} (precision : ℕ)
    (A : Matrix r c ℚ) (i : r) (j : c) (h : A i j = 0) :
    matrix precision A i j = 0 := by simp [matrix, h]

theorem matrix_entry_error {r c : Type*} (precision : ℕ)
    (A : Matrix r c ℚ) (i : r) (j : c) :
    |matrix precision A i j - A i j| ≤ 1 / (2 * (2 : ℚ) ^ precision) :=
  nearest_error precision (A i j)

/-- Equal occurrences receive the same dyadic, so exact symmetry is preserved. -/
theorem matrix_symmetric {d : Type*} (precision : ℕ) (A : Matrix d d ℚ)
    (h : A.IsSymm) : (matrix precision A).IsSymm := by
  ext i j
  exact congrArg (fun q => (nearest precision q).value) (congrFun (congrFun h i) j)

/-- A finite coordinate read within half a grid width followed by rounding
within half a grid width incurs at most one grid width of total error. -/
theorem finite_read_then_round (exactValue readValue roundedValue spacing : ℝ)
    (hread : |readValue - exactValue| ≤ spacing / 2)
    (hround : |roundedValue - readValue| ≤ spacing / 2) :
    |roundedValue - exactValue| ≤ spacing := by
  calc
    |roundedValue - exactValue| = |(roundedValue - readValue) + (readValue - exactValue)| := by
      congr 1
      ring
    _ ≤ |roundedValue - readValue| + |readValue - exactValue| := abs_add_le _ _
    _ ≤ spacing := by linarith

end Maxwell.Logical.Rounding
