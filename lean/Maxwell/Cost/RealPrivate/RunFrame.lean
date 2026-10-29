import Maxwell.Cost.RealPrivate.CallerFrame

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

/-- The full cap controller additionally owns its fuel, status and active
words. Input buffers, the origin, caller data and output channels survive. -/
structure RunFrame (origin : ℕ) (s t : RAMState) : Prop where
  words : ∀ j, 32 ≤ j → j < origin → t.words j = s.words j
  indices : ∀ j, 11 ≤ j → j < origin → (j < 165 ∨ 171 < j) →
    t.indices j = s.indices j
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput

theorem RunFrame.refl (origin : ℕ) (s : RAMState) : RunFrame origin s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl⟩

theorem RunFrame.trans {origin : ℕ} {s t u : RAMState}
    (h : RunFrame origin s t) (h' : RunFrame origin t u) : RunFrame origin s u :=
  ⟨fun j hj ho => (h'.words j hj ho).trans (h.words j hj ho),
    fun j hj ho hm => (h'.indices j hj ho hm).trans (h.indices j hj ho hm),
    h'.output.trans h.output, h'.indexOutput.trans h.indexOutput⟩

theorem CallerFrame.runFrame {origin : ℕ} {s t : RAMState}
    (h : CallerFrame origin s t) : RunFrame origin s t :=
  ⟨h.words, fun j hj ho hm => h.indices j hj ho (by omega), h.output, h.indexOutput⟩

theorem RunFrame.inputs {origin : ℕ} {L : Layout} {B : InputBuffer} {input : RAMInput}
    {s t : RAMState} (h : RunFrame origin s t) (high : 256 ≤ origin)
    (hs : Inputs L origin B input s) : Inputs L origin B input t := by
  refine ⟨?_, ?_, ?_, ?_, hs.real_low, hs.index_low, hs.real_high, hs.index_high,
    ?_, ?_, hs.real_outside, hs.index_outside⟩
  · rw [h.indices realInputBase (by decide) (by unfold realInputBase; omega) (by left; decide)]
    exact hs.real_base
  · rw [h.indices realInputLength (by decide) (by unfold realInputLength; omega) (by left; decide)]
    exact hs.real_length
  · rw [h.indices indexInputBase (by decide) (by unfold indexInputBase; omega) (by left; decide)]
    exact hs.index_base
  · rw [h.indices indexInputLength (by decide) (by unfold indexInputLength; omega) (by left; decide)]
    exact hs.index_length
  · intro j hj
    rw [h.words _ (by have := hs.real_low; omega) (hs.real_high j hj)]
    exact hs.real_cells j hj
  · intro j hj
    rw [h.indices _ (by have := hs.index_low; omega) (hs.index_high j hj)
      (by right; have := hs.index_low; omega)]
    exact hs.index_cells j hj

theorem runFrame_put (s : Store) (origin r v : ℕ)
    (hr : r < 11 ∨ (165 ≤ r ∧ r ≤ 171) ∨ origin ≤ r) :
    RunFrame origin s.val (s.put r v).val := by
  refine ⟨fun _ _ _ => rfl, ?_, rfl, rfl⟩
  intro j hj ho hm
  simp [show j ≠ r by omega]

theorem Represents.put_control {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val) (r v : ℕ)
    (hr : r = fuelRegister ∨ r = statusRegister ∨ r = activeRegister) :
    Represents origin source written (s.put r v).val := by
  have hsmall : r < 256 := by rcases hr with rfl | rfl | rfl <;> decide
  have hn (j : ℕ) (hj : j ≠ fuelRegister ∧ j ≠ statusRegister ∧ j ≠ activeRegister) : j ≠ r := by
    rcases hr with rfl | rfl | rfl
    · exact hj.1
    · exact hj.2.1
    · exact hj.2.2
  have hb (bank a : ℕ) : slot origin bank a ≠ r := slot_ne_small h.high bank a r hsmall
  refine ⟨h.high, ?_, ?_, ?_, ?_, h.words, ?_, ?_, ?_, h.real_output, ?_, ?_, ?_, h.random_cursor⟩
  · simpa [hn originRegister (by decide)] using h.origin_word
  · simpa [hn zeroRegister (by decide)] using h.zero
  · simpa [hn oneRegister (by decide)] using h.one
  · simpa [hn sourcePC (by decide)] using h.pc
  · intro a; simpa [hb] using h.indices a
  · simpa [hn realOutputLength (by decide)] using h.real_output_length
  · simpa [hn indexOutputLength (by decide)] using h.index_output_length
  · intro j hj; simpa [hb] using h.index_output j hj
  · simpa [hn logLength (by decide)] using h.log_length
  · intro j hj; simpa [hb] using h.log_cells j hj

end Maxwell.Cost.RealPrivate
