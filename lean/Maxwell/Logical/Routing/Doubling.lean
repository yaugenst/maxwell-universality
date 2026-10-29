import Maxwell.Logical.Routing.CycleColor
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! Materialized jump/minimum arrays for finite permutation-cycle minima.
Each doubling round allocates two vectors and only reads the previous vectors. -/

namespace Maxwell.Logical.Routing.Doubling

open Equiv
open Maxwell.Logical.Routing.CycleColor

/-- Two actual arrays, rather than an unevaluated recursive lookup function. -/
structure State (α : Type*) (n : ℕ) where
  jump : Vector α n
  minimum : Vector α n

def jumpAt {α : Type*} {n : ℕ} (index : α ≃ Fin n) (state : State α n) (x : α) : α :=
  state.jump.get (index x)

def minAt {α : Type*} {n : ℕ} (index : α ≃ Fin n) (state : State α n) (x : α) : α :=
  state.minimum.get (index x)

/-- Materialize the permutation and its one-token minima. -/
def initial {α : Type*} {n : ℕ} (index : α ≃ Fin n) (p : Perm α) : State α n :=
  ⟨Vector.ofFn (fun i => p (index.symm i)), Vector.ofFn index.symm⟩

/-- One parallel pass: at every index read the saved jump, compose the saved
jumps, and minimize the two saved orbit halves. -/
def step {α : Type*} [LinearOrder α] {n : ℕ} (index : α ≃ Fin n) (state : State α n) : State α n :=
  ⟨Vector.ofFn (fun i => jumpAt index state (state.jump.get i)),
   Vector.ofFn (fun i => min (state.minimum.get i) (minAt index state (state.jump.get i)))⟩

/-- Execute the indicated number of materialized array passes. The saved
state is shared by every lookup in the following pass. -/
def run {α : Type*} [LinearOrder α] {n : ℕ} (index : α ≃ Fin n) (p : Perm α) : ℕ → State α n
  | 0 => initial index p
  | rounds + 1 => let saved := run index p rounds; step index saved

@[simp] theorem jumpAt_initial {α : Type*} {n : ℕ} (index : α ≃ Fin n) (p : Perm α) (x : α) :
    jumpAt index (initial index p) x = p x := by simp [jumpAt, initial, Vector.get, Fin.cast]

@[simp] theorem minAt_initial {α : Type*} {n : ℕ} (index : α ≃ Fin n) (p : Perm α) (x : α) :
    minAt index (initial index p) x = x := by simp [minAt, initial, Vector.get, Fin.cast]

@[simp] theorem jumpAt_step {α : Type*} [LinearOrder α] {n : ℕ} (index : α ≃ Fin n) (state : State α n) (x : α) :
    jumpAt index (step index state) x = jumpAt index state (jumpAt index state x) := by
  simp [jumpAt, step, Vector.get, Fin.cast]

@[simp] theorem minAt_step {α : Type*} [LinearOrder α] {n : ℕ} (index : α ≃ Fin n) (state : State α n) (x : α) :
    minAt index (step index state) x = min (minAt index state x) (minAt index state (jumpAt index state x)) := by
  simp [minAt, step, jumpAt, Vector.get, Fin.cast]

/-- Exact semantics of the arrays for a block of consecutive orbit positions. -/
structure Covers {α : Type*} [LinearOrder α] {n : ℕ}
    (index : α ≃ Fin n) (p : Perm α) (length : ℕ) (state : State α n) : Prop where
  jump : ∀ x, jumpAt index state x = (p ^ length) x
  member : ∀ x, ∃ k < length, minAt index state x = (p ^ k) x
  lower : ∀ x k, k < length → minAt index state x ≤ (p ^ k) x

theorem initial_covers {α : Type*} [LinearOrder α] {n : ℕ} (index : α ≃ Fin n) (p : Perm α) :
    Covers index p 1 (initial index p) where
  jump x := by simp
  member x := ⟨0, by omega, by simp⟩
  lower x k hk := by
    have he : k = 0 := by omega
    simp [he]

theorem step_covers {α : Type*} [LinearOrder α] {n : ℕ} (index : α ≃ Fin n) (p : Perm α)
    (length : ℕ) (state : State α n) (h : Covers index p length state) :
    Covers index p (2 * length) (step index state) := by
  have hpow (x : α) (k : ℕ) : (p ^ (length + k)) x = (p ^ k) ((p ^ length) x) := by
    rw [Nat.add_comm length k, pow_add, Perm.mul_apply]
  constructor
  · intro x
    rw [jumpAt_step, h.jump, h.jump, show 2 * length = length + length by omega, hpow]
  · intro x
    rw [minAt_step]
    by_cases hle : minAt index state x ≤ minAt index state (jumpAt index state x)
    · obtain ⟨k, hk, he⟩ := h.member x
      exact ⟨k, by omega, by rw [min_eq_left hle, he]⟩
    · obtain ⟨k, hk, he⟩ := h.member (jumpAt index state x)
      refine ⟨length + k, by omega, ?_⟩
      rw [min_eq_right (le_of_not_ge hle), he, h.jump, hpow]
  · intro x k hk
    rw [minAt_step]
    by_cases hl : k < length
    · exact (min_le_left _ _).trans (h.lower x k hl)
    · have hkl : k = length + (k - length) := by omega
      have hh := h.lower (jumpAt index state x) (k - length) (by omega)
      rw [h.jump] at hh
      rw [hkl, hpow, h.jump]
      exact (min_le_right _ _).trans hh

/-- After k stored passes the arrays cover exactly 2^k orbit positions. -/
theorem run_covers {α : Type*} [LinearOrder α] {n : ℕ} (index : α ≃ Fin n) (p : Perm α) (rounds : ℕ) :
    Covers index p (2 ^ rounds) (run index p rounds) := by
  induction rounds with
  | zero => exact initial_covers index p
  | succ rounds ih =>
    simpa only [run, pow_succ'] using step_covers index p (2 ^ rounds) (run index p rounds) ih

/-- Every point in one permutation cycle occurs within its first card(alpha)
positions, using its actual minimal period rather than the permutation order. -/
theorem sameCycle_bounded_power {α : Type*} [Fintype α] (p : Perm α) {x y : α}
    (h : p.SameCycle x y) : ∃ k < Fintype.card α, (p ^ k) x = y := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts x)
  have hb := Function.minimalPeriod_le_card (f := (p : α → α)) (x := x)
  refine ⟨k % Function.minimalPeriod p x, (Nat.mod_lt k hp).trans_le hb, ?_⟩
  have he := Function.iterate_mod_minimalPeriod_eq (f := (p : α → α)) (x := x) (n := k)
  simpa only [← Perm.coe_pow, hk] using he

/-- The materialized minimum arrays equal the finite-orbit specification
once their covered block is at least the number of tokens. -/
theorem run_minimum_eq_orbitMin {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}
    (index : α ≃ Fin n) (p : Perm α) (rounds : ℕ) (hsize : n ≤ 2 ^ rounds) (x : α) :
    minAt index (run index p rounds) x = orbitMin p x := by
  have hc : Fintype.card α = n := by simpa only [Fintype.card_fin] using Fintype.card_congr index
  have h := run_covers index p rounds
  apply le_antisymm
  · obtain ⟨k, hk, he⟩ := sameCycle_bounded_power p (orbitMin_sameCycle p x)
    rw [← he]
    exact h.lower x k (by omega)
  · obtain ⟨k, _, he⟩ := h.member x
    rw [he]
    apply Finset.min'_le
    apply (mem_evenOrbit p x _).mpr
    exact (Perm.SameCycle.refl p x).pow_right

/-- ceil(log2 n) materialized passes suffice for every input permutation. -/
theorem logarithmic_run_correct {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}
    (index : α ≃ Fin n) (p : Perm α) (x : α) :
    minAt index (run index p (Nat.clog 2 n)) x = orbitMin p x :=
  run_minimum_eq_orbitMin index p _ (Nat.le_pow_clog (by omega) n) x

/-- Compute the split bits in one final stored pass after sharing the completed
minimum arrays. Each output uses two minimum reads and one comparison. -/
def colors {α : Type*} [LinearOrder α] {n : ℕ}
    (index : α ≃ Fin n) (a b : Perm α) : Vector Bool n :=
  let saved := run index (a * b) (Nat.clog 2 n)
  Vector.ofFn (fun i => decide (minAt index saved (index.symm i) <
    minAt index saved (a (index.symm i))))

/-- The executable array split is exactly the proved alternating-cycle split. -/
theorem colors_correct {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}
    (index : α ≃ Fin n) (a b : Perm α) (x : α) :
    (colors index a b).get (index x) = CycleColor.color a b x := by
  simp [colors, Vector.get, Fin.cast, logarithmic_run_correct, CycleColor.color]

end Maxwell.Logical.Routing.Doubling
