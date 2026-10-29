import Maxwell.Cost.PhysicalMaterial.DescriptorRead
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Maxwell.Cost.PhysicalMaterial.Descriptors
open scoped BigOperators

/-- A descriptor's exact unsigned rational strength. -/
def strengthPair {n : ℕ} (d : Data n) (i : Fin n) : ℕ × ℕ :=
  (value d i 3, value d i 4)

/-- The actual loop overwrites its selected pair at each successful test. The
geometric disjointness theorem below identifies this with the unique hit. -/
def selectedThrough {n : ℕ} (d : Data n) (hit : Fin n → Bool) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 => if hk : k < n then
      if hit ⟨k, hk⟩ then strengthPair d ⟨k, hk⟩ else selectedThrough d hit k
    else selectedThrough d hit k

@[simp] theorem selectedThrough_zero {n : ℕ} (d : Data n) (hit : Fin n → Bool) :
    selectedThrough d hit 0 = (0, 1) := rfl

theorem selectedThrough_step {n : ℕ} (d : Data n) (hit : Fin n → Bool) (i : Fin n) :
    selectedThrough d hit (i.val+1) =
      if hit i then strengthPair d i else selectedThrough d hit i.val := by
  simp [selectedThrough, i.isLt]

theorem selectedThrough_none {n : ℕ} (d : Data n) (hit : Fin n → Bool)
    (h : ∀ i, hit i = false) (k : ℕ) : selectedThrough d hit k = (0, 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [selectedThrough, h, ih]

theorem selectedThrough_unique {n : ℕ} (d : Data n) (hit : Fin n → Bool) (i : Fin n)
    (h : ∀ j, hit j = true ↔ j = i) (k : ℕ) (hk : k ≤ n) :
    selectedThrough d hit k = if i.val < k then strengthPair d i else (0, 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k < n := by omega
    have ih' := ih (by omega)
    rw [selectedThrough, dite_eq_left hkn]
    by_cases hki : k = i.val
    · have hi : (⟨k, hkn⟩ : Fin n) = i := Fin.ext hki
      rw [hi, ite_eq_left ((h i).mpr rfl), ite_eq_left (by omega)]
    · have hji : (⟨k, hkn⟩ : Fin n) ≠ i := fun he => hki (congrArg Fin.val he)
      have hh : hit ⟨k, hkn⟩ = false := by
        cases he : hit ⟨k, hkn⟩
        · rfl
        · exact False.elim (hji ((h _).mp he))
      simp only [hh, Bool.false_eq_true, ↓reduceIte, ih']
      have heq : (i.val < k+1) ↔ (i.val < k) := by omega
      simp only [heq]

theorem selectedThrough_bits {n : ℕ} (d : Data n) (hit : Fin n → Bool) (B : ℕ)
    (hB : 0 < B) (hbits : ∀ i, (strengthPair d i).1.bits.length ≤ B ∧
      (strengthPair d i).2.bits.length ≤ B) (k : ℕ) :
    (selectedThrough d hit k).1.bits.length ≤ B ∧
      (selectedThrough d hit k).2.bits.length ≤ B := by
  induction k with
  | zero => simpa using (show 0 ≤ B ∧ 1 ≤ B by omega)
  | succ k ih =>
    simp only [selectedThrough]
    split
    · split
      · exact hbits _
      · exact ih
    · exact ih

theorem selectedThrough_den_pos {n : ℕ} (d : Data n) (hit : Fin n → Bool)
    (hpos : ∀ i, 0 < (strengthPair d i).2) (k : ℕ) :
    0 < (selectedThrough d hit k).2 := by
  induction k with
  | zero => simp [selectedThrough]
  | succ k ih =>
    simp only [selectedThrough]
    split
    · split
      · exact hpos _
      · exact ih
    · exact ih

/-- For disjoint physical blocks the selected rational is exactly the sum of
all defect indicators at the cell, including the case of no matching block. -/
theorem selectedThrough_value {n : ℕ} (d : Data n) (hit : Fin n → Bool)
    (hunique : ∀ i j, hit i = true → hit j = true → i = j) :
    ((selectedThrough d hit n).1 : ℚ) / (selectedThrough d hit n).2 =
      ∑ i, if hit i then ((strengthPair d i).1 : ℚ) / (strengthPair d i).2 else 0 := by
  by_cases hex : ∃ i, hit i = true
  · obtain ⟨i, hi⟩ := hex
    have hiff (j : Fin n) : hit j = true ↔ j = i :=
      ⟨fun hj => hunique j i hj hi, fun he => he ▸ hi⟩
    rw [selectedThrough_unique d hit i hiff n le_rfl, ite_eq_left i.isLt]
    symm
    rw [Finset.sum_eq_single i]
    · simp only [hi, ↓reduceIte]
    · intro j _ hji
      have hj : hit j = false := by
        cases hh : hit j
        · rfl
        · exact False.elim (hji ((hiff j).mp hh))
      simp only [hj, Bool.false_eq_true, ↓reduceIte]
    · simp
  · have hh (i : Fin n) : hit i = false := by
      cases he : hit i
      · rfl
      · exact False.elim (hex ⟨i, he⟩)
    rw [selectedThrough_none d hit hh]
    simp [hh]

end Maxwell.Cost.PhysicalMaterial.Descriptors
