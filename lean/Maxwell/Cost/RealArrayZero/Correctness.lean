import Maxwell.Cost.RealArrayZero.Program

namespace Maxwell.Cost.RealArrayZero
open RealSparse (execute execute_sound)
open RealSimulation.Control
set_option maxRecDepth 20000

theorem advanced_ready (dst n k : ℕ) (s : RAMState)
    (h : Ready dst n k s) : Ready dst n (k + 1) (advanced s) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [advanced, RAMState.setIndex, h.count]
  · simp [advanced, RAMState.setIndex, RAMState.setWord, h.one]
  · simp [advanced, RAMState.setIndex, h.target, Nat.add_assoc]
  · simp [advanced, RAMState.setIndex, RAMState.setWord, h.total]
  · simp [advanced, RAMState.setIndex, RAMState.setWord, Function.update, h.zero]
  · intro j hj
    by_cases he : j = k
    · subst j
      simp [advanced, RAMState.setIndex, RAMState.setWord, h.target]
    · have hjk : j < k := by omega
      simp [advanced, RAMState.setIndex, RAMState.setWord, h.target, Function.update, he, h.output j hjk]

theorem advanced_frame (dst n k : ℕ) (s : RAMState)
    (h : Ready dst n k s) (hk : k < n) : Frame dst n s (advanced s) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro i _ ho
    simp [advanced, RAMState.setIndex, RAMState.setWord, h.target, show i ≠ dst + k by omega]
  · intro i hi
    simp [advanced, RAMState.setIndex, RAMState.setWord, show i ≠ 0 by omega, show i ≠ 3 by omega]

theorem scan (input : RAMInput) (tape : ℕ → Bool)
    (dst n remaining k : ℕ) (s : RAMState) (h : Ready dst n k s) (hc : k + remaining = n) :
    ∃ t : RAMState, Steps (program.next input tape) (5 * remaining) s t ∧
      Ready dst n n t ∧ Frame dst n s t := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, h, Frame.refl dst n s⟩
  | succ remaining ih =>
    have hk : k < n := by omega
    obtain ⟨t, ht, hr, hf⟩ := ih (k + 1) (advanced s) (advanced_ready dst n k s h) (by omega)
    refine ⟨t, ?_, hr, (advanced_frame dst n k s h hk).trans hf⟩
    convert (execute_sound _ (cycle input tape dst n k s h hk)).trans ht using 1
    omega

theorem terminates (input : RAMInput) (tape : ℕ → Bool)
    (dst n : ℕ) (s : RAMState) (hpc : s.pc = 0) (hd : s.indices 56 = dst) (hn : s.indices 57 = n) :
    ∃ t : RAMState, Terminates (program.next input tape) (5 * n + 5) s t ∧
      t.pc = 9 ∧ (∀ j < n, t.words (dst + j) = 0) ∧ Frame dst n s t := by
  have hi := execute_sound _ (initialize_steps input tape s hpc)
  obtain ⟨t, ht, hr, hf⟩ := scan input tape dst n n 0 (initialized s)
    (initialized_ready dst n s hpc hd hn) (by omega)
  have hexit : Steps (program.next input tape) 1 t {t with pc := 9} := by
    apply execute_sound
    simp [execute, program, Machine.next, hr.pc, hr.count, hr.total]
  have hframe := (initialized_frame dst n s).trans hf
  refine ⟨{t with pc := 9}, ?_, rfl, hr.output,
    ⟨hframe.words, hframe.indices, hframe.output, hframe.indexOutput, hframe.randomCursor⟩⟩
  convert ((hi.trans ht).trans hexit).terminates
    (Terminates.halt _ (by simp [program, Machine.next])) using 1
  omega

theorem executes (input : RAMInput) (tape : ℕ → Bool)
    (dst n : ℕ) (s : Store) (hd : s.val.indices 56 = dst) (hn : s.val.indices 57 = n) :
    ∃ t : Store, Executes input tape (.call program) (5 * n + 6) s t ∧
      (∀ j < n, t.val.words (dst + j) = 0) ∧ Frame dst n s.val t.val := by
  obtain ⟨t, ht, hpc, ho, hf⟩ := terminates input tape dst n s.val s.property hd hn
  refine ⟨Store.ofState t, ?_, ho, ⟨hf.words, hf.indices, hf.output, hf.indexOutput, hf.randomCursor⟩⟩
  exact Executes.call program s t (5 * n + 5) ht.toSteps (by simp [program, hpc])

end Maxwell.Cost.RealArrayZero
