import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic

/-! Alternating-cycle splitting of two fixed-point-free incidence pairings. -/

namespace Maxwell.Logical.Routing.CycleColor

open Equiv

/-- An odd alternating word is a conjugate of a shorter odd alternating word. -/
theorem odd_word_rec {α : Type*} (a b : Perm α) (n : ℕ) :
    (a * b) ^ (n + 1) * a = a * ((b * a) ^ n * b) * a := by
  calc
    (a * b) ^ (n + 1) * a = ((a * b) ^ n * a) * b * a := by simp only [pow_succ, mul_assoc]
    _ = a * ((b * a) ^ n * b) * a := by rw [mul_pow_mul]; simp only [mul_assoc]

/-- No odd alternating walk can close: peeling its first and last paired
steps would eventually produce a fixed point of one incidence pairing. -/
theorem odd_word_no_fixed {α : Type*} (a b : Perm α)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hfa : ∀ x, a x ≠ x) (hfb : ∀ x, b x ≠ x) (n : ℕ) (x : α) :
    ((a * b) ^ n * a) x ≠ x := by
  induction n generalizing a b x with
  | zero => simpa only [pow_zero, one_mul] using hfa x
  | succ n ih =>
    rw [odd_word_rec]
    intro he
    have hh : ((b * a) ^ n * b) (a x) = a x := by
      apply a.injective
      simpa only [Perm.mul_apply, ha x] using he
    exact ih b a hb ha hfb hfa (a x) hh

/-- The even and odd halves of an alternating cycle are disjoint. -/
theorem not_sameCycle_pair {α : Type*} [Finite α] (a b : Perm α)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hfa : ∀ x, a x ≠ x) (hfb : ∀ x, b x ≠ x) (x : α) :
    ¬(a * b).SameCycle x (a x) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  apply odd_word_no_fixed a b ha hb hfa hfb n (a x)
  simpa only [Perm.mul_apply, ha x] using hn

/-- A cycle's even-indexed tokens. This finite set defines the mathematical
split independently of the subsequent traversal implementation. -/
noncomputable def evenOrbit {α : Type*} [Fintype α] (p : Perm α) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (p.SameCycle x)

@[simp] theorem mem_evenOrbit {α : Type*} [Fintype α] (p : Perm α) (x y : α) :
    y ∈ evenOrbit p x ↔ p.SameCycle x y := by
  classical
  simp [evenOrbit]

theorem evenOrbit_nonempty {α : Type*} [Fintype α] (p : Perm α) (x : α) :
    (evenOrbit p x).Nonempty := ⟨x, (mem_evenOrbit p x x).mpr (.refl _ _)⟩

theorem evenOrbit_eq {α : Type*} [Fintype α] (p : Perm α) {x y : α} (h : p.SameCycle x y) :
    evenOrbit p x = evenOrbit p y := by
  ext z
  simp only [mem_evenOrbit]
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

noncomputable def orbitMin {α : Type*} [Fintype α] [LinearOrder α] (p : Perm α) (x : α) : α :=
  (evenOrbit p x).min' (evenOrbit_nonempty p x)

theorem orbitMin_sameCycle {α : Type*} [Fintype α] [LinearOrder α] (p : Perm α) (x : α) :
    p.SameCycle x (orbitMin p x) :=
  (mem_evenOrbit p x _).mp (Finset.min'_mem _ _)

theorem orbitMin_eq {α : Type*} [Fintype α] [LinearOrder α] (p : Perm α) {x y : α} (h : p.SameCycle x y) :
    orbitMin p x = orbitMin p y := by
  unfold orbitMin
  congr 1
  exact evenOrbit_eq p h

theorem orbitMin_eq_iff {α : Type*} [Fintype α] [LinearOrder α] (p : Perm α) (x y : α) :
    orbitMin p x = orbitMin p y ↔ p.SameCycle x y := by
  constructor
  · intro he
    have hx := orbitMin_sameCycle p x
    have hy := orbitMin_sameCycle p y
    rw [he] at hx
    exact hx.trans hy.symm
  · exact orbitMin_eq p

/-- Orient the two disjoint halves of each alternating component by their
least token, giving a definite split rather than an assumed coloring. -/
noncomputable def color {α : Type*} [Fintype α] [LinearOrder α] (a b : Perm α) (x : α) : Bool :=
  decide (orbitMin (a * b) x < orbitMin (a * b) (a x))

/-- The constructed split alternates at every source incidence pair. -/
theorem color_pair_a {α : Type*} [Fintype α] [LinearOrder α] (a b : Perm α)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hfa : ∀ x, a x ≠ x) (hfb : ∀ x, b x ≠ x) (x : α) :
    color a b (a x) = !(color a b x) := by
  have hne : orbitMin (a * b) x ≠ orbitMin (a * b) (a x) := by
    rw [ne_eq, orbitMin_eq_iff]
    exact not_sameCycle_pair a b ha hb hfa hfb x
  simp only [color, ha x]
  by_cases hlt : orbitMin (a * b) x < orbitMin (a * b) (a x)
  · have hnl := not_lt_of_ge (le_of_lt hlt)
    simp only [hlt, hnl, decide_true, decide_false, Bool.not_true]
  · have hrev := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    simp only [hlt, hrev, decide_true, decide_false, Bool.not_false]

/-- The same constructed split alternates at every target incidence pair. -/
theorem color_pair_b {α : Type*} [Fintype α] [LinearOrder α] (a b : Perm α)
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hfa : ∀ x, a x ≠ x) (hfb : ∀ x, b x ≠ x) (x : α) :
    color a b (b x) = !(color a b x) := by
  have hleft : orbitMin (a * b) (b x) = orbitMin (a * b) (a x) := by
    apply orbitMin_eq
    refine ⟨1, ?_⟩
    simp only [zpow_one, Perm.mul_apply, hb x]
  have hright : orbitMin (a * b) (a (b x)) = orbitMin (a * b) x := by
    apply orbitMin_eq
    exact (Perm.SameCycle.refl (a * b) x).apply_left
  have hh := color_pair_a a b ha hb hfa hfb x
  simpa only [color, hleft, hright, ha x] using hh

end Maxwell.Logical.Routing.CycleColor
