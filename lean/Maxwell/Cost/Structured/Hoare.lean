import Maxwell.Cost.Structured.Syntax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Bounded-loop rules for the actual structured execution relation. Every
body iteration is supplied by a real `Executes` derivation; the rules retain
every body charge and every loop test, including the final false test. -/

namespace Maxwell.Cost.Structured

open scoped BigOperators

/-- A countdown invariant and charged body executions give a complete finite
loop execution. `cap k` bounds the iteration leaving remaining count k+1. -/
theorem loop_bounded
    (input : List Bool) (randomTape : ℕ → Bool) (register : ℕ) (body : Code)
    (invariant : ℕ → Store → Prop) (cap : ℕ → ℕ)
    (stop : ∀ s, invariant 0 s → s.val.registers register = false)
    (nextTest : ∀ k s, invariant (k + 1) s → s.val.registers register = true)
    (iteration : ∀ k s, invariant (k + 1) s →
      ∃ cost t, Executes input randomTape body cost s t ∧ invariant k t ∧ cost ≤ cap k)
    (count : ℕ) (s : Store) (hs : invariant count s) :
    ∃ cost t, Executes input randomTape (.loop register body) cost s t ∧
      invariant 0 t ∧ cost ≤ 1 + count + ∑ k ∈ Finset.range count, cap k := by
  induction count generalizing s with
  | zero =>
    exact ⟨1, s, Executes.done (stop s hs), hs, by simp⟩
  | succ count ih =>
    obtain ⟨firstCost, middle, firstRun, hmiddle, hfirst⟩ := iteration count s hs
    obtain ⟨restCost, finish, restRun, hfinish, hrest⟩ := ih middle hmiddle
    refine ⟨1 + firstCost + restCost, finish,
      Executes.more (nextTest count s hs) firstRun restRun, hfinish, ?_⟩
    rw [Finset.sum_range_succ]
    omega

/-- A uniform per-iteration cap gives the standard linear charged bound. -/
theorem loop_constant_bound
    (input : List Bool) (randomTape : ℕ → Bool) (register : ℕ) (body : Code)
    (invariant : ℕ → Store → Prop) (cap : ℕ)
    (stop : ∀ s, invariant 0 s → s.val.registers register = false)
    (nextTest : ∀ k s, invariant (k + 1) s → s.val.registers register = true)
    (iteration : ∀ k s, invariant (k + 1) s →
      ∃ cost t, Executes input randomTape body cost s t ∧ invariant k t ∧ cost ≤ cap)
    (count : ℕ) (s : Store) (hs : invariant count s) :
    ∃ cost t, Executes input randomTape (.loop register body) cost s t ∧
      invariant 0 t ∧ cost ≤ 1 + count * (cap + 1) := by
  obtain ⟨cost, t, hr, ht, hc⟩ :=
    loop_bounded input randomTape register body invariant (fun _ => cap)
      stop nextTest iteration count s hs
  refine ⟨cost, t, hr, ht, ?_⟩
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

/-- The same rule can consume an explicit integer rank on machine stores.
The rank must decrease by one in every actual executed body. -/
theorem loop_rank_bound
    (input : List Bool) (randomTape : ℕ → Bool) (register : ℕ) (body : Code)
    (property : Store → Prop) (remaining : Store → ℕ) (cap : ℕ)
    (stop : ∀ s, property s → remaining s = 0 → s.val.registers register = false)
    (nextTest : ∀ s, property s → 0 < remaining s → s.val.registers register = true)
    (iteration : ∀ s, property s → 0 < remaining s →
      ∃ cost t, Executes input randomTape body cost s t ∧ property t ∧
        remaining t + 1 = remaining s ∧ cost ≤ cap)
    (s : Store) (hs : property s) :
    ∃ cost t, Executes input randomTape (.loop register body) cost s t ∧
      property t ∧ remaining t = 0 ∧ cost ≤ 1 + remaining s * (cap + 1) := by
  have hstop : ∀ t, (property t ∧ remaining t = 0) → t.val.registers register = false := by
    intro t ht
    exact stop t ht.1 ht.2
  have hcontinue : ∀ k t, (property t ∧ remaining t = k + 1) →
      t.val.registers register = true := by
    intro k t ht
    exact nextTest t ht.1 (by omega)
  have hiteration : ∀ k t, (property t ∧ remaining t = k + 1) →
      ∃ cost u, Executes input randomTape body cost t u ∧
        (property u ∧ remaining u = k) ∧ cost ≤ cap := by
    intro k t ht
    obtain ⟨cost, u, hr, hu, hdecrease, hc⟩ := iteration t ht.1 (by omega)
    exact ⟨cost, u, hr, ⟨hu, by omega⟩, hc⟩
  obtain ⟨cost, t, hr, ht, hc⟩ := loop_constant_bound input randomTape register body
    (fun k t => property t ∧ remaining t = k) cap hstop hcontinue hiteration
      (remaining s) s ⟨hs, rfl⟩
  exact ⟨cost, t, hr, ht.1, ht.2, hc⟩

end Maxwell.Cost.Structured
