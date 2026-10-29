import Maxwell.Cost.RealPrecision.Program

namespace Maxwell.Cost.RealPrecision
open RealSparse (execute execute_sound)
open RealSimulation.Control
set_option maxRecDepth 20000

theorem advanced_ready (coefficient n k : ℕ) (s : RAMState) (h : Ready coefficient n k s) :
    Ready coefficient n (k + 1) (advanced s) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [advanced, RAMState.setIndex, h.count]
  · simp [advanced, RAMState.setIndex, h.one]
  · simp [advanced, RAMState.setIndex, h.power, pow_succ, Nat.mul_two]
  · simp [advanced, RAMState.setIndex, h.coefficient]
  · simp [advanced, RAMState.setIndex, h.precision, h.coefficient, Nat.mul_add, Nat.add_assoc]
  · simp [advanced, RAMState.setIndex, h.total]

theorem advanced_frame (s : RAMState) : Frame s (advanced s) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro i hi hn
  simp [advanced, RAMState.setIndex, hn, show i ≠ 0 by omega, show i ≠ 2 by omega]

theorem scan (coefficient n : ℕ) (input : RAMInput) (tape : ℕ → Bool)
    (remaining k : ℕ) (s : RAMState) (h : Ready coefficient n k s) (hc : k + remaining = n.size) :
    ∃ t : RAMState, Steps ((program coefficient).next input tape) (5 * remaining) s t ∧
      Ready coefficient n n.size t ∧ Frame s t := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k = n.size := by omega
    subst k
    exact ⟨s, Steps.refl s, h, Frame.refl s⟩
  | succ remaining ih =>
    have hk : k < n.size := by omega
    obtain ⟨t, ht, hr, hf⟩ := ih (k + 1) (advanced s) (advanced_ready coefficient n k s h) (by omega)
    refine ⟨t, ?_, hr, (advanced_frame s).trans hf⟩
    convert (execute_sound _ (cycle coefficient n k input tape s h hk)).trans ht using 1
    omega

theorem terminates (coefficient n : ℕ) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc = 0) (hn : s.indices 53 = n) :
    ∃ t : RAMState, Terminates ((program coefficient).next input tape) (5 * n.size + 6) s t ∧
      t.pc = 10 ∧ t.indices 27 = 7 + coefficient * n.size ∧ Frame s t := by
  have hi := execute_sound _ (initialize_steps coefficient input tape s hpc)
  obtain ⟨t, ht, hr, hf⟩ := scan coefficient n input tape n.size 0 (initialized coefficient s)
    (initialized_ready coefficient n s hpc hn) (by omega)
  have hexit : Steps ((program coefficient).next input tape) 1 t {t with pc := 10} := by
    apply execute_sound
    have hp : ¬2 ^ n.size ≤ n := Nat.not_le.mpr (Nat.lt_size_self n)
    simp [execute, program, Machine.next, hr.pc, hr.power, hr.total, hp]
  have hframe := (initialized_frame coefficient s).trans hf
  refine ⟨{t with pc := 10}, ?_, rfl, hr.precision,
    ⟨hframe.words, hframe.indices, hframe.output, hframe.indexOutput, hframe.randomCursor⟩⟩
  convert ((hi.trans ht).trans hexit).terminates
    (Terminates.halt _ (by simp [program, Machine.next])) using 1
  omega

/-- Actual precision generation uses only doubling, comparison, and
addition. Its fixed instruction list does not contain input-dependent constants. -/
theorem executes (coefficient n : ℕ) (input : RAMInput) (tape : ℕ → Bool)
    (s : Store) (hn : s.val.indices 53 = n) :
    ∃ t : Store, Executes input tape (.call (program coefficient)) (5 * n.size + 7) s t ∧
      t.val.indices 27 = 7 + coefficient * n.size ∧ Frame s.val t.val := by
  obtain ⟨t, ht, hpc, hp, hf⟩ := terminates coefficient n input tape s.val s.property hn
  refine ⟨Store.ofState t, ?_, hp, ⟨hf.words, hf.indices, hf.output, hf.indexOutput, hf.randomCursor⟩⟩
  exact Executes.call (program coefficient) s t (5 * n.size + 6) ht.toSteps (by simp [program, hpc])

end Maxwell.Cost.RealPrecision
