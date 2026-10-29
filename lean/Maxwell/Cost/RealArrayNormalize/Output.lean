import Maxwell.Cost.RealArrayNormalize.Maximum

namespace Maxwell.Cost.RealArrayNormalize
open RealSparse (execute execute_add execute_sound)
open RealNormalize (maxAbs scale normalized)
set_option maxRecDepth 20000

structure OutputReady (s : RAMState) (byCount : Bool) (base n k : ℕ) (v : ℕ → ℝ) : Prop where
  pc : s.pc = 30
  one : s.indices 1 = 1
  total : s.indices 2 = n
  count : s.indices 3 = k
  pointer : s.indices 24 = base + k
  maximum : s.words 0 = maxAbs v n
  zero : s.words 2 = 0
  divisor : s.words 7 = scale byCount n v
  values : ∀ j < n, s.words (base + j) = if j < k then normalized byCount n v j else v j

noncomputable def outputInitialized (s : RAMState) (byCount : Bool) : RAMState :=
  let t := ({s with pc := 27}).setWord 7 (if byCount then s.words 0 * s.words 1 else s.words 0)
  let t := t.setIndex 3 0
  t.setIndex 24 (s.indices 25)

theorem output_initialize (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (base n : ℕ) (v : ℕ → ℝ) (s : RAMState) (h : MaxReady s base n n v) :
    execute ((program byCount).next input tape) 4 s = some (outputInitialized s byCount) := by
  cases byCount <;> simp [execute, program, Machine.next, h.pc, h.total, h.count,
    outputInitialized, RAMState.setWord, RAMState.setIndex]

theorem outputInitialized_ready (byCount : Bool) (base n : ℕ) (v : ℕ → ℝ)
    (s : RAMState) (hbase : 32 ≤ base) (h : MaxReady s base n n v) :
    OutputReady (outputInitialized s byCount) byCount base n 0 v := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp [outputInitialized, RAMState.setWord, RAMState.setIndex,
    h.one, h.total, h.origin, h.maximum, h.realCount, h.zero, scale]
  intro j hj
  have hneq : base + j ≠ 7 := by omega
  simpa [outputInitialized, RAMState.setWord, RAMState.setIndex, hneq] using h.values j hj

theorem outputInitialized_frame (byCount : Bool) (base n : ℕ) (s : RAMState) :
    Frame base n s (outputInitialized s byCount) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro i hi _
    simp [outputInitialized, RAMState.setWord, RAMState.setIndex, show i ≠ 7 by omega]
  · intro i hi hne
    simp [outputInitialized, RAMState.setWord, RAMState.setIndex, show i ≠ 3 by omega, hne]

noncomputable def outputComputed (s : RAMState) (x : ℝ) : RAMState :=
  let t := ({s with pc := 31}).setWord 5 x
  let t := t.setWord 5 (if s.words 0 ≤ s.words 2 then 0 else x / s.words 7)
  {t with pc := 37}

noncomputable def outputAdvanced (s : RAMState) (x : ℝ) : RAMState :=
  let t := outputComputed s x
  let t := t.setWord (s.indices 24) (if s.words 0 ≤ s.words 2 then 0 else x / s.words 7)
  let t := t.setIndex 3 (s.indices 3 + 1)
  let t := t.setIndex 24 (s.indices 24 + 1)
  {t with pc := 30}

theorem output_cycle (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (base n k : ℕ) (v : ℕ → ℝ) (s : RAMState) (h : OutputReady s byCount base n k v)
    (hk : k < n) :
    execute ((program byCount).next input tape) 9 s = some (outputAdvanced s (v k)) := by
  have hnot : ¬ n ≤ k := by omega
  have hv : s.words (base + k) = v k := by simpa using h.values k hk
  have hfirst : execute ((program byCount).next input tape) 5 s = some (outputComputed s (v k)) := by
    by_cases hz : s.words 0 ≤ s.words 2 <;>
      simp [execute, program, Machine.next, h.pc, h.total, h.count, h.pointer, hv, hnot, hz,
        outputComputed, RAMState.setWord]
  rw [show 9 = 5 + 4 from rfl, execute_add, hfirst, Option.bind_some]
  simp [execute, program, Machine.next, outputComputed, outputAdvanced, h.one,
    RAMState.setWord, RAMState.setIndex]

theorem outputAdvanced_ready (byCount : Bool) (base n k : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (hbase : 32 ≤ base) (h : OutputReady s byCount base n k v) :
    OutputReady (outputAdvanced s (v k)) byCount base n (k + 1) v := by
  have hlow : ∀ i < 8, i ≠ base + k := by omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp [outputAdvanced, outputComputed, RAMState.setWord, RAMState.setIndex,
    h.one, h.total, h.count, h.pointer, h.maximum, h.zero, h.divisor, hlow, Nat.add_assoc]
  intro j hj
  have h5 : base + j ≠ 5 := by omega
  by_cases he : j = k
  · subst j
    simp [normalized]
  · have hneq : base + j ≠ base + k := by omega
    have hlt : j ≤ k ↔ j < k := by omega
    simpa [Function.update_apply, hneq, he, h5, hlt] using h.values j hj

theorem outputAdvanced_frame (byCount : Bool) (base n k : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (h : OutputReady s byCount base n k v) (hk : k < n) :
    Frame base n s (outputAdvanced s (v k)) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro i hi hout
    have h5 : i ≠ 5 := by omega
    have hneq : i ≠ base + k := by rcases hout with hlt | hge <;> omega
    simp [outputAdvanced, outputComputed, RAMState.setWord, RAMState.setIndex, h5, h.pointer, hneq]
  · intro i hi hne
    simp [outputAdvanced, outputComputed, RAMState.setWord, RAMState.setIndex, show i ≠ 3 by omega, hne]

theorem output_scan (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (base n : ℕ) (v : ℕ → ℝ) (hbase : 32 ≤ base)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (h : OutputReady s byCount base n k v)
    (hcount : k + remaining = n) :
    ∃ t : RAMState, Steps ((program byCount).next input tape) (9 * remaining) s t ∧
      OutputReady t byCount base n n v ∧ Frame base n s t := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, h, Frame.refl base n s⟩
  | succ remaining ih =>
    obtain ⟨t, ht, hr, hf⟩ := ih (outputAdvanced s (v k)) (k + 1)
      (outputAdvanced_ready byCount base n k v s hbase h) (by omega)
    refine ⟨t, ?_, hr, (outputAdvanced_frame byCount base n k v s h (by omega)).trans hf⟩
    convert (execute_sound _ (output_cycle byCount input tape base n k v s h (by omega))).trans ht using 1
    omega

end Maxwell.Cost.RealArrayNormalize
