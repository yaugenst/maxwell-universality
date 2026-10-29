import Maxwell.Cost.RealArrayNormalize.Program

namespace Maxwell.Cost.RealArrayNormalize
open RealSparse (execute execute_add execute_sound)
open RealNormalize (maxAbs)
set_option maxRecDepth 20000

theorem max_cycle (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (base n k : ℕ) (v : ℕ → ℝ) (s : RAMState) (h : MaxReady s base n k v) (hk : k < n) :
    execute ((program byCount).next input tape) 13 s = some (maxAdvanced s (v k)) := by
  have hnot : ¬ n ≤ k := by omega
  have hfirst : execute ((program byCount).next input tape) 6 s = some (maxMiddle s (v k)) := by
    by_cases hx : v k ≤ -v k
    · have hneg : v k ≤ 0 := by linarith
      simp [execute, program, Machine.next, h.pc, h.total, h.count, h.pointer, h.values k hk,
        h.minus, hnot, hx, maxMiddle, RAMState.setWord, abs_of_nonpos hneg]
    · have hpos : 0 ≤ v k := by linarith
      simp [execute, program, Machine.next, h.pc, h.total, h.count, h.pointer, h.values k hk,
        h.minus, hnot, hx, maxMiddle, RAMState.setWord, abs_of_nonneg hpos]
  rw [show 13 = 6 + 7 from rfl, execute_add, hfirst, Option.bind_some]
  by_cases hx : s.words 0 ≤ |v k|
  · simp [execute, program, Machine.next, h.one, h.count, h.pointer, h.unit, hx,
      maxMiddle, maxAdvanced, RAMState.setWord, RAMState.setIndex]
  · simp [execute, program, Machine.next, h.one, h.count, h.pointer, h.unit, hx,
      maxMiddle, maxAdvanced, RAMState.setWord, RAMState.setIndex, max_eq_left (le_of_not_ge hx)]

theorem maxAdvanced_ready (base n k : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (hbase : 32 ≤ base) (h : MaxReady s base n k v) :
    MaxReady (maxAdvanced s (v k)) base n (k + 1) v := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp [maxAdvanced, maxMiddle, RAMState.setWord, RAMState.setIndex,
    h.one, h.total, h.count, h.pointer, h.origin, h.maximum, h.realCount, h.zero, h.minus,
    h.unit, maxAbs, Nat.add_assoc]
  intro j hj
  have hneq : ∀ i < 8, base + j ≠ i := by omega
  simpa [maxAdvanced, maxMiddle, RAMState.setWord, RAMState.setIndex, Function.update_apply,
    hneq, show base ≠ 0 by omega] using h.values j hj

theorem maxAdvanced_frame (base n : ℕ) (s : RAMState) (x : ℝ) :
    Frame base n s (maxAdvanced s x) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro i hi _
    have hn : ∀ j < 8, i ≠ j := by omega
    simp [maxAdvanced, maxMiddle, RAMState.setWord, RAMState.setIndex, hn]
  · intro i hi hne
    have hn : i ≠ 3 := by omega
    simp [maxAdvanced, maxMiddle, RAMState.setWord, RAMState.setIndex, hn, hne]

theorem max_scan (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (base n : ℕ) (v : ℕ → ℝ) (hbase : 32 ≤ base)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (h : MaxReady s base n k v)
    (hcount : k + remaining = n) :
    ∃ t : RAMState, Steps ((program byCount).next input tape) (13 * remaining) s t ∧
      MaxReady t base n n v ∧ Frame base n s t := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, h, Frame.refl base n s⟩
  | succ remaining ih =>
    obtain ⟨t, ht, hr, hf⟩ := ih (maxAdvanced s (v k)) (k + 1)
      (maxAdvanced_ready base n k v s hbase h) (by omega)
    refine ⟨t, ?_, hr, (maxAdvanced_frame base n s (v k)).trans hf⟩
    convert (execute_sound _ (max_cycle byCount input tape base n k v s h (by omega))).trans ht using 1
    omega

end Maxwell.Cost.RealArrayNormalize
