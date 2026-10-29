import Maxwell.Cost.RealPrivate.Macros
import Maxwell.Cost.RealPrivate.Representation

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem slot_ne_small {origin : ℕ} (high : 256 ≤ origin) (bank a j : ℕ)
    (small : j < 256) : slot origin bank a ≠ j := by
  have := slot_ge_origin origin bank a
  omega

@[simp] theorem slot_same_bank (origin bank a b : ℕ) :
    slot origin bank a = slot origin bank b ↔ a = b := by
  unfold slot
  omega

theorem slot_different {origin a b bank bank' : ℕ} (hb : bank < 4) (hb' : bank' < 4)
    (hne : bank ≠ bank') : slot origin bank a ≠ slot origin bank' b := by
  intro h
  exact hne ((slot_injective origin bank bank' a b hb hb').mp h).1

theorem Represents.put_pc {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val) (pc : ℕ) :
    Represents origin {source with pc := pc} written (s.put sourcePC pc).val := by
  have hn (bank a : ℕ) : slot origin bank a ≠ sourcePC :=
    slot_ne_small h.high bank a sourcePC (by decide)
  refine ⟨h.high, ?_, ?_, ?_, ?_, h.words, ?_, ?_, ?_, h.real_output, ?_, ?_, ?_, h.random_cursor⟩
  · simpa [originRegister, sourcePC] using h.origin_word
  · simpa [zeroRegister, sourcePC] using h.zero
  · simpa [oneRegister, sourcePC] using h.one
  · simp
  · intro a; simpa [hn] using h.indices a
  · simpa [realOutputLength, sourcePC] using h.real_output_length
  · simpa [indexOutputLength, sourcePC] using h.index_output_length
  · intro j hj; simpa [hn] using h.index_output j hj
  · simpa [logLength, sourcePC] using h.log_length
  · intro j hj; simpa [hn] using h.log_cells j hj

theorem Represents.private_word {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val) (address : ℕ) (v : ℝ) :
    Represents origin {source with words := Function.update source.words address v} written
      (putWord s (slot origin 0 address) v).val := by
  refine ⟨h.high, h.origin_word, h.zero, h.one, h.pc, ?_, h.indices,
    h.real_output_length, h.index_output_length, ?_, h.index_output,
    h.log_length, h.log_cells, h.random_cursor⟩
  · intro a
    simp only [putWord_words, slot_same_bank, Function.update_apply]
    split <;> simp_all only [h.words]
  · intro j hj
    have hn : slot origin 1 j ≠ slot origin 0 address := slot_different (by decide) (by decide) (by decide)
    simpa [hn] using h.real_output j hj

theorem Represents.private_index {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val) (address v : ℕ) :
    Represents origin {source with indices := Function.update source.indices address v} written
      (s.put (slot origin 0 address) v).val := by
  have hn (j : ℕ) (hj : j < 256) : j ≠ slot origin 0 address :=
    (slot_ne_small h.high 0 address j hj).symm
  have hout (j : ℕ) : slot origin 1 j ≠ slot origin 0 address :=
    slot_different (by decide) (by decide) (by decide)
  have hlog (j : ℕ) : slot origin 2 j ≠ slot origin 0 address :=
    slot_different (by decide) (by decide) (by decide)
  refine ⟨h.high, ?_, ?_, ?_, ?_, h.words, ?_, ?_, ?_, h.real_output, ?_, ?_, ?_, h.random_cursor⟩
  · simpa [hn originRegister (by decide)] using h.origin_word
  · simpa [hn zeroRegister (by decide)] using h.zero
  · simpa [hn oneRegister (by decide)] using h.one
  · simpa [hn sourcePC (by decide)] using h.pc
  · intro a
    simp only [Store.put_indices, slot_same_bank, Function.update_apply]
    split <;> simp_all only [h.indices]
  · simpa [hn realOutputLength (by decide)] using h.real_output_length
  · simpa [hn indexOutputLength (by decide)] using h.index_output_length
  · intro j hj; simpa [hout] using h.index_output j hj
  · simpa [hn logLength (by decide)] using h.log_length
  · intro j hj; simpa [hlog] using h.log_cells j hj

theorem Covered.private_word {source : RAMState} {written : List ℕ}
    (h : Covered source written) (address : ℕ) (v : ℝ) :
    Covered {source with words := Function.update source.words address v} (address :: written) := by
  intro a ha
  have hn : a ≠ address := by intro he; subst a; exact ha (List.mem_cons_self)
  have hw : a ∉ written := by intro hm; exact ha (List.mem_cons_of_mem _ hm)
  simpa [Function.update_of_ne hn] using h a hw

theorem Covered.private_index {source : RAMState} {written : List ℕ}
    (h : Covered source written) (address v : ℕ) :
    Covered {source with indices := Function.update source.indices address v} (address :: written) := by
  intro a ha
  have hn : a ≠ address := by intro he; subst a; exact ha (List.mem_cons_self)
  have hw : a ∉ written := by intro hm; exact ha (List.mem_cons_of_mem _ hm)
  simpa [Function.update_of_ne hn] using h a hw

end Maxwell.Cost.RealPrivate
