import Maxwell.Cost.RealArrayNormalize.Output

namespace Maxwell.Cost.RealArrayNormalize
open RealSparse (execute execute_sound)
open RealNormalize (maxAbs scale normalized)
set_option maxRecDepth 20000

/-- Both passes operate on the caller's actual array. Count multiplication,
maximum comparisons, the zero case and every overwrite are charged. -/
theorem terminates (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (base n : ℕ) (v : ℕ → ℝ) (s : RAMState) (hbase : 32 ≤ base)
    (hpc : s.pc = 0) (hb : s.indices 25 = base) (hn : s.indices 26 = n)
    (hv : ∀ j < n, s.words (base + j) = v j) :
    ∃ t : RAMState, Terminates ((program byCount).next input tape) (22 * n + 15) s t ∧
      t.pc = 41 ∧ t.words 0 = maxAbs v n ∧ t.words 7 = scale byCount n v ∧
      (∀ j < n, t.words (base + j) = normalized byCount n v j) ∧ Frame base n s t := by
  have hi := execute_sound _ (initialize_steps byCount input tape s hpc)
  obtain ⟨a, ha, hra, hfa⟩ := max_scan byCount input tape base n v hbase n (initialized s) 0
    (initialized_ready base n v s hbase hpc hb hn hv) (by omega)
  have hbridge := execute_sound _ (output_initialize byCount input tape base n v a hra)
  obtain ⟨t, ht, hrt, hft⟩ := output_scan byCount input tape base n v hbase n
    (outputInitialized a byCount) 0 (outputInitialized_ready byCount base n v a hbase hra) (by omega)
  have he : Steps ((program byCount).next input tape) 1 t {t with pc := 41} := by
    apply execute_sound
    simp [execute, program, Machine.next, hrt.pc, hrt.total, hrt.count]
  have hframe := ((initialized_frame base n s).trans hfa).trans
    ((outputInitialized_frame byCount base n a).trans hft)
  refine ⟨{t with pc := 41}, ?_, rfl, hrt.maximum, hrt.divisor, ?_, ?_⟩
  · convert ((((hi.trans ha).trans hbridge).trans ht).trans he).terminates
      (Terminates.halt _ (by simp [program, Machine.next])) using 1
    omega
  · intro j hj
    simpa [hj] using hrt.values j hj
  · exact ⟨hframe.words, hframe.indices, hframe.output, hframe.indexOutput, hframe.randomCursor⟩

theorem run (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (base n : ℕ) (v : ℕ → ℝ) (s : RAMState) (hbase : 32 ≤ base)
    (hpc : s.pc = 0) (hb : s.indices 25 = base) (hn : s.indices 26 = n)
    (hv : ∀ j < n, s.words (base + j) = v j) :
    ∃ t : RAMState,
      (runCapped ((program byCount).next input tape) (22 * n + 16) s).finished = some t ∧
      (runCapped ((program byCount).next input tape) (22 * n + 16) s).instructions = 22 * n + 15 ∧
      t.words 7 = scale byCount n v ∧
      (∀ j < n, t.words (base + j) = normalized byCount n v j) ∧ Frame base n s t := by
  obtain ⟨t, ht, _, _, hscale, hvalues, hframe⟩ := terminates byCount input tape base n v s hbase hpc hb hn hv
  obtain ⟨hf, hcost⟩ := runCapped_of_terminates _ ht
  exact ⟨t, hf, hcost, hscale, hvalues, hframe⟩

end Maxwell.Cost.RealArrayNormalize
