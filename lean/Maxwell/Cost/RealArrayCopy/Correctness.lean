import Maxwell.Cost.RealArrayCopy.Program

namespace Maxwell.Cost.RealArrayCopy
open RealSparse (execute execute_sound)
open RealSimulation.Control
set_option maxRecDepth 20000

theorem advanced_ready (negate : Bool) (src dst n k : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (hsrc : 8 ≤ src) (hsep : src + n ≤ dst) (h : Ready negate src dst n k v s) (hk : k < n) :
    Ready negate src dst n (k + 1) v (advanced s) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [advanced, RAMState.setIndex, h.count]
  · simp [advanced, RAMState.setIndex, RAMState.setWord, h.one]
  · simp [advanced, RAMState.setIndex, h.source, Nat.add_assoc]
  · simp [advanced, RAMState.setIndex, h.target, Nat.add_assoc]
  · simp [advanced, RAMState.setIndex, RAMState.setWord, h.total]
  · simp [advanced, RAMState.setIndex, RAMState.setWord, h.target,
      show (1 : ℕ) ≠ dst + k by omega, h.factor]
  · intro j hj
    simp [advanced, RAMState.setIndex, RAMState.setWord, h.target,
      show src + j ≠ dst + k by omega, Function.update, show src ≠ 0 by omega, h.input j hj]
  · intro j hj
    by_cases he : j = k
    · subst j
      simp [advanced, RAMState.setIndex, RAMState.setWord, h.target, h.source, h.input k hk, h.factor, mul_comm]
    · have hjk : j < k := by omega
      simp [advanced, RAMState.setIndex, RAMState.setWord, h.target,
        Function.update, he, show dst ≠ 0 by omega, h.output j hjk]

theorem advanced_frame (negate : Bool) (src dst n k : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (h : Ready negate src dst n k v s) (hk : k < n) : Frame dst n s (advanced s) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro i hi ho
    simp [advanced, RAMState.setIndex, RAMState.setWord, h.target,
      show i ≠ dst + k by omega, show i ≠ 0 by omega]
  · intro i hi
    simp [advanced, RAMState.setIndex, RAMState.setWord, show i ≠ 0 by omega,
      show i ≠ 2 by omega, show i ≠ 3 by omega]

theorem scan (negate : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (src dst n : ℕ) (v : ℕ → ℝ) (hsrc : 8 ≤ src) (hsep : src + n ≤ dst)
    (remaining k : ℕ) (s : RAMState) (h : Ready negate src dst n k v s) (hc : k + remaining = n) :
    ∃ t : RAMState, Steps ((program negate).next input tape) (8 * remaining) s t ∧
      Ready negate src dst n n v t ∧ Frame dst n s t := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, h, Frame.refl dst n s⟩
  | succ remaining ih =>
    have hk : k < n := by omega
    obtain ⟨t, ht, hr, hf⟩ := ih (k + 1) (advanced s) (advanced_ready negate src dst n k v s hsrc hsep h hk) (by omega)
    refine ⟨t, ?_, hr, (advanced_frame negate src dst n k v s h hk).trans hf⟩
    convert (execute_sound _ (cycle negate input tape src dst n k v s h hk)).trans ht using 1
    omega

theorem terminates (negate : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (src dst n : ℕ) (v : ℕ → ℝ) (s : RAMState) (hsrc : 8 ≤ src) (hsep : src + n ≤ dst)
    (hpc : s.pc = 0) (hs : s.indices 55 = src) (hd : s.indices 56 = dst) (hn : s.indices 57 = n)
    (hv : ∀ j < n, s.words (src + j) = v j) :
    ∃ t : RAMState, Terminates ((program negate).next input tape) (8 * n + 6) s t ∧
      t.pc = 13 ∧ (∀ j < n, t.words (dst + j) = sign negate * v j) ∧
      (∀ j < n, t.words (src + j) = v j) ∧ Frame dst n s t := by
  have hi := execute_sound _ (initialize_steps negate input tape s hpc)
  obtain ⟨t, ht, hr, hf⟩ := scan negate input tape src dst n v hsrc hsep n 0 (initialized negate s)
    (initialized_ready negate src dst n v s hsrc hpc hs hd hn hv) (by omega)
  have hexit : Steps ((program negate).next input tape) 1 t {t with pc := 13} := by
    apply execute_sound
    simp [execute, program, Machine.next, hr.pc, hr.count, hr.total]
  have hframe := (initialized_frame negate dst n s).trans hf
  refine ⟨{t with pc := 13}, ?_, rfl, hr.output, hr.input,
    ⟨hframe.words, hframe.indices, hframe.output, hframe.indexOutput, hframe.randomCursor⟩⟩
  convert ((hi.trans ht).trans hexit).terminates
    (Terminates.halt _ (by simp [program, Machine.next])) using 1
  omega

theorem executes (negate : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (src dst n : ℕ) (v : ℕ → ℝ) (s : Store) (hsrc : 8 ≤ src) (hsep : src + n ≤ dst)
    (hs : s.val.indices 55 = src) (hd : s.val.indices 56 = dst) (hn : s.val.indices 57 = n)
    (hv : ∀ j < n, s.val.words (src + j) = v j) :
    ∃ t : Store, Executes input tape (.call (program negate)) (8 * n + 7) s t ∧
      (∀ j < n, t.val.words (dst + j) = sign negate * v j) ∧
      (∀ j < n, t.val.words (src + j) = v j) ∧ Frame dst n s.val t.val := by
  obtain ⟨t, ht, hpc, ho, hi, hf⟩ := terminates negate input tape src dst n v s.val hsrc hsep s.property hs hd hn hv
  refine ⟨Store.ofState t, ?_, ho, hi, ⟨hf.words, hf.indices, hf.output, hf.indexOutput, hf.randomCursor⟩⟩
  exact Executes.call (program negate) s t (8 * n + 6) ht.toSteps (by simp [program, hpc])

end Maxwell.Cost.RealArrayCopy
