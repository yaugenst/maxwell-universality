import Maxwell.Logical.Circuit
import Mathlib.Data.Rat.Cast.Order

/-! Finite coefficient alphabet and actually allocated gate equations.
Distinct binary parents are represented by a proof, so coefficients cannot
accidentally combine into a value outside the fixed alphabet.
-/

namespace Maxwell.Logical

inductive Weight where
  | one | negOne | half | negHalf
  deriving DecidableEq

namespace Weight

def value : Weight → ℚ
  | .one => 1
  | .negOne => -1
  | .half => 1 / 2
  | .negHalf => -1 / 2

theorem abs_le_one (w : Weight) : |w.value| ≤ 1 := by cases w <;> norm_num [value]
theorem ne_zero (w : Weight) : w.value ≠ 0 := by cases w <;> norm_num [value]
theorem neg_mem (w : Weight) : ∃ v : Weight, -w.value = v.value := by
  cases w
  · exact ⟨.negOne, by norm_num [value]⟩
  · exact ⟨.one, by norm_num [value]⟩
  · exact ⟨.negHalf, by norm_num [value]⟩
  · exact ⟨.half, by norm_num [value]⟩

end Weight

inductive Gate (dimension : ℕ) where
  | zero
  | unary (parent : Fin dimension) (weight : Weight)
  | binary (left right : Fin dimension) (distinct : left ≠ right)
      (leftWeight rightWeight : Weight)

namespace Gate

def coefficient {d : ℕ} : Gate d → Fin d → ℚ
  | .zero => fun _ => 0
  | .unary parent weight => fun i => if i = parent then weight.value else 0
  | .binary left right _ leftWeight rightWeight =>
      fun i => (if i = left then leftWeight.value else 0) +
        (if i = right then rightWeight.value else 0)

def parents {d : ℕ} : Gate d → Finset (Fin d)
  | .zero => ∅
  | .unary parent _ => {parent}
  | .binary left right _ _ _ => {left, right}

theorem parents_card_le_two {d : ℕ} (g : Gate d) : g.parents.card ≤ 2 := by
  cases g with
  | zero => simp [parents]
  | unary => simp [parents]
  | binary left right distinct _ _ => simp [parents, distinct]

theorem coefficient_ne_zero_iff {d : ℕ} (g : Gate d) (i : Fin d) :
    g.coefficient i ≠ 0 ↔ i ∈ g.parents := by
  cases g with
  | zero => simp [parents, coefficient]
  | unary parent weight => simp [parents, coefficient, weight.ne_zero]
  | binary left right distinct leftWeight rightWeight =>
      by_cases hl : i = left
      · subst i
        simp [parents, coefficient, distinct, leftWeight.ne_zero]
      · by_cases hr : i = right
        · subst i
          simp [parents, coefficient, hl, rightWeight.ne_zero]
        · simp [parents, coefficient, hl, hr]

theorem coefficient_alphabet {d : ℕ} (g : Gate d) (i : Fin d) :
    g.coefficient i = 0 ∨ ∃ w : Weight, g.coefficient i = w.value := by
  cases g with
  | zero => exact Or.inl rfl
  | unary parent weight =>
      by_cases h : i = parent
      · exact Or.inr ⟨weight, by simp [coefficient, h]⟩
      · exact Or.inl (by simp [coefficient, h])
  | binary left right distinct leftWeight rightWeight =>
      by_cases hl : i = left
      · subst i
        exact Or.inr ⟨leftWeight, by simp [coefficient, distinct]⟩
      · by_cases hr : i = right
        · subst i
          exact Or.inr ⟨rightWeight, by simp [coefficient, Ne.symm distinct]⟩
        · exact Or.inl (by simp [coefficient, hl, hr])

theorem coefficient_abs_le_one {d : ℕ} (g : Gate d) (i : Fin d) :
    |g.coefficient i| ≤ 1 := by
  rcases g.coefficient_alphabet i with h | ⟨w, h⟩
  · simp [h]
  · rw [h]
    exact w.abs_le_one

def equation {d : ℕ} (g : Gate d) : Fin (d + 1) → ℚ :=
  Fin.snoc (fun i => -g.coefficient i) 1

def equationSupport {d : ℕ} (g : Gate d) : Finset (Fin (d + 1)) :=
  insert (Fin.last d) (g.parents.image Fin.castSucc)

theorem equation_ne_zero_iff {d : ℕ} (g : Gate d) (i : Fin (d + 1)) :
    g.equation i ≠ 0 ↔ i ∈ g.equationSupport := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [equation, equationSupport]
  · simp [equation, equationSupport, g.coefficient_ne_zero_iff]

theorem equation_support_card_le_three {d : ℕ} (g : Gate d) :
    g.equationSupport.card ≤ 3 := by
  have hi := Finset.card_image_le (f := @Fin.castSucc d) (s := g.parents)
  have hp := g.parents_card_le_two
  have hc := Finset.card_insert_le (Fin.last d) (g.parents.image Fin.castSucc)
  change (insert (Fin.last d) (g.parents.image Fin.castSucc)).card ≤ 3
  omega

theorem equation_alphabet {d : ℕ} (g : Gate d) (i : Fin (d + 1)) :
    g.equation i = 0 ∨ ∃ w : Weight, g.equation i = w.value := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact Or.inr ⟨.one, by simp [equation, Weight.value]⟩
  · simp only [equation, Fin.snoc_castSucc]
    rcases g.coefficient_alphabet j with h | ⟨w, h⟩
    · exact Or.inl (by simp [h])
    · rw [h]
      exact Or.inr w.neg_mem

def append {n d : ℕ} (c : Circuit n d) (g : Gate d) : Circuit n (d + 1) :=
  c.append (fun i => (g.coefficient i : ℝ))

/-- The newly allocated equation computes exactly the selected gate,
with its own residual included. -/
theorem append_equation {n d : ℕ} (c : Circuit n d) (g : Gate d)
    (input : Fin n → ℝ) (error : Fin (d + 1) → ℝ) :
    (g.append c).evaluate input error (Fin.last d) -
      ∑ i, (g.coefficient i : ℝ) * c.evaluate input (fun j => error j.castSucc) i =
        error (Fin.last d) := by
  simp [append, Circuit.evaluate_append_last]

end Gate
end Maxwell.Logical
