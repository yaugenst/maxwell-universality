import Maxwell.Cost.RealTransposePreserve.Program

namespace Maxwell.Cost.RealTransposePreserve
open RealSimulation.Control
open RealSparse (execute_sound)
set_option maxRecDepth 20000

theorem product_executes (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ t : Store, Executes (RealSparse.input es vector) tape (.call RealSparse.program)
      (15 * es.length + 8) (Store.ofState RAMState.initial) t ∧
      (∀ j, t.val.words (16 + j) = RealSparse.transposeSum es vector j) ∧
      t.val.output = [] ∧ t.val.indexOutput = [] ∧ t.val.randomCursor = 0 := by
  have hi := execute_sound _ (RealSparse.initialize_steps es vector tape)
  obtain ⟨t, ht, hpc, hm, hr, ho⟩ := RealSparse.loop es vector tape es.length
    (RealSparse.initialized es.length) 0 (RealSparse.initialized_ready _) (by omega)
  have he : Terminates (RealSparse.program.next (RealSparse.input es vector) tape)
      (15 * es.length + 7) RAMState.initial t := by
    convert hi.terminates ht using 1
    omega
  refine ⟨Store.ofState t, ?_, ?_, ho, ?_, hr⟩
  · exact Executes.call _ _ _ _ he.toSteps (by simp [RealSparse.program, hpc])
  · intro j
    simpa [Store.ofState, RealSparse.initialized, RAMState.setIndex, RAMState.initial, RealSparse.transposeSum] using hm j
  · have hp : ∀ s t : RAMState,
        RealSparse.program.next (RealSparse.input es vector) tape s = some t →
        t.indexOutput = s.indexOutput := by
      intro s t h
      by_cases hlt : s.pc < 22
      · interval_cases hpc' : s.pc <;>
          simp [RealSparse.program, Machine.next, hpc', RAMState.setIndex, RAMState.setWord] at h <;>
          try { cases h; rfl }
      · have hget : RealSparse.program.code[s.pc]? = none := by
          apply List.getElem?_eq_none
          simpa [RealSparse.program] using Nat.le_of_not_gt hlt
        simp [Machine.next, hget] at h
    have hpreserve : ∀ {n : ℕ} {a b : RAMState},
        Steps (RealSparse.program.next (RealSparse.input es vector) tape) n a b →
        b.indexOutput = a.indexOutput := by
      intro n a b hs
      induction hs with
      | refl => rfl
      | @step n a b c hn hs ih => exact ih.trans (hp a b hn)
    exact hpreserve he.toSteps

/-- The product is computed from the original typed COO input and copied
into a disjoint high buffer by actual charged code. No state is reinitialized. -/
theorem executes (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ t : Store, Executes (RealSparse.input es vector) tape code (23 * es.length + 24)
      (Store.ofState RAMState.initial) t ∧
      (∀ j < es.length, t.val.words (100 + 6 * es.length + j) =
        RealSparse.transposeSum es vector j) ∧
      t.val.indices 55 = 16 ∧ t.val.indices 56 = 100 + 6 * es.length ∧
      t.val.indices 57 = es.length ∧
      t.val.output = [] ∧ t.val.indexOutput = [] ∧ t.val.randomCursor = 0 := by
  obtain ⟨a, hea, hqa, hoa, hia, hra⟩ := product_executes es vector tape
  let b := prepared es.length a
  obtain ⟨t, het, hqt, _, hf⟩ := RealArrayCopy.executes false (RealSparse.input es vector) tape
    16 (100 + 6 * es.length) es.length (RealSparse.transposeSum es vector) b (by omega) (by omega)
    (by simp [b, prepared, Store.ofState, RAMState.setIndex])
    (by simp [b, prepared, Store.ofState, RAMState.setIndex]; omega)
    (by simp [b, prepared, Store.ofState, RAMState.setIndex])
    (by intro j _; exact hqa j)
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, hf.output.trans hoa, hf.indexOutput.trans hia, hf.randomCursor.trans hra⟩
  · convert hea.seq ((prepare_executes es vector tape a).seq het) using 1 <;> try rfl
    omega
  · intro j hj
    simpa [RealArrayCopy.sign] using hqt j hj
  · simpa [b, prepared, Store.ofState, RAMState.setIndex] using hf.indices 55 (by omega)
  · have hh := hf.indices 56 (by omega)
    simp only [b, prepared, Store.ofState, RAMState.setIndex] at hh
    simp at hh
    omega
  · simpa [b, prepared, Store.ofState, RAMState.setIndex] using hf.indices 57 (by omega)

theorem run (es : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ t : RAMState,
      (program.run (RealSparse.input es vector) tape (23 * es.length + 25)).finished = some t ∧
      (program.run (RealSparse.input es vector) tape (23 * es.length + 25)).instructions =
        23 * es.length + 24 ∧
      (∀ j < es.length, t.words (100 + 6 * es.length + j) = RealSparse.transposeSum es vector j) ∧
      t.output = [] ∧ t.indexOutput = [] ∧ t.randomCursor = 0 := by
  obtain ⟨t, ht, hq, _, _, _, ho, hi, hr⟩ := executes es vector tape
  obtain ⟨hf, hc⟩ := ht.compiled_run (23 * es.length + 25) (by omega)
  exact ⟨t.place code.size, hf, hc, hq, ho, hi, hr⟩

end Maxwell.Cost.RealTransposePreserve
