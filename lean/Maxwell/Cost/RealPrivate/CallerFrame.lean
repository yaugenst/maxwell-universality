import Maxwell.Cost.RealPrivate.Frame

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

/-- A translated source instruction preserves caller memory, input metadata,
fuel/status/active controller words and both external output channels.
Its random cursor may advance only as recorded by `Represents`. -/
structure CallerFrame (origin : ℕ) (s t : RAMState) : Prop where
  words : ∀ j, 32 ≤ j → j < origin → t.words j = s.words j
  indices : ∀ j, 11 ≤ j → j < origin → (j < 167 ∨ 170 < j) →
    t.indices j = s.indices j
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput

theorem CallerFrame.refl (origin : ℕ) (s : RAMState) : CallerFrame origin s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl⟩

theorem CallerFrame.trans {origin : ℕ} {s t u : RAMState}
    (h : CallerFrame origin s t) (h' : CallerFrame origin t u) : CallerFrame origin s u :=
  ⟨fun j hj ho => (h'.words j hj ho).trans (h.words j hj ho),
    fun j hj ho hm => (h'.indices j hj ho hm).trans (h.indices j hj ho hm),
    h'.output.trans h.output, h'.indexOutput.trans h.indexOutput⟩

theorem CallerFrame.inputs {origin : ℕ} {L : Layout} {B : InputBuffer} {input : RAMInput}
    {s t : RAMState} (h : CallerFrame origin s t) (high : 256 ≤ origin)
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

theorem callerFrame_put (s : Store) (origin r v : ℕ)
    (hr : r < 11 ∨ (167 ≤ r ∧ r ≤ 170) ∨ origin ≤ r) :
    CallerFrame origin s.val (s.put r v).val := by
  refine ⟨fun _ _ _ => rfl, ?_, rfl, rfl⟩
  intro j hj ho hm
  simp [show j ≠ r by omega]

theorem callerFrame_word (s : Store) (origin r : ℕ) (v : ℝ)
    (hr : r < 32 ∨ origin ≤ r) : CallerFrame origin s.val (putWord s r v).val := by
  refine ⟨?_, fun _ _ _ _ => rfl, rfl, rfl⟩
  intro j hj ho
  simp [show j ≠ r by omega]

theorem callerFrame_drawn (s : Store) (origin dst : ℕ) (b : Bool) (hd : dst < 32) :
    CallerFrame origin s.val (drawn s dst b).val := by
  have h := callerFrame_word s origin dst (if b then 1 else 0) (Or.inl hd)
  exact ⟨h.words, h.indices, h.output, h.indexOutput⟩

theorem callerFrame_indexed (s : Store) (origin address dst : ℕ) (hd : dst < 11) :
    CallerFrame origin s.val (indexed s address dst).val :=
  (callerFrame_put s origin pointerRegister _ (Or.inl (by decide))).trans
    (callerFrame_put _ origin dst _ (Or.inl hd))

theorem callerFrame_worded (s : Store) (origin address dst : ℕ) (hd : dst < 32) :
    CallerFrame origin s.val (worded s address dst).val :=
  (callerFrame_put s origin pointerRegister _ (Or.inl (by decide))).trans
    (callerFrame_word _ origin dst _ (Or.inl hd))

theorem callerFrame_logged (s : Store) (origin : ℕ)
    (ho : s.val.indices originRegister = origin) : CallerFrame origin s.val (logged s).val := by
  apply (callerFrame_put s origin pointerRegister _ (Or.inl (by decide))).trans
  apply (callerFrame_put _ origin _ _ (Or.inr (Or.inr ?_))).trans
  · exact callerFrame_put _ origin logLength _ (Or.inr (Or.inl (by decide)))
  · rw [ho]; exact slot_ge_origin _ _ _

theorem callerFrame_indexSet (s : Store) (origin address src : ℕ)
    (ho : s.val.indices originRegister = origin) (high : 256 ≤ origin) :
    CallerFrame origin s.val (indexSet s address src).val := by
  let s0 := s.put pointerRegister (slot (s.val.indices originRegister) 0 address)
  let s1 := s0.put (slot (s.val.indices originRegister) 0 address) (s.val.indices src)
  let s2 := s1.put coordinateRegister address
  have hn : originRegister ≠ slot origin 0 address :=
    (slot_ne_small high 0 address originRegister (by decide)).symm
  have h160 : s.val.indices 160 = origin := ho
  have hn160 : 160 ≠ slot origin 0 address := hn
  have hh : s2.val.indices originRegister = origin := by
    simp [s2, s1, s0, h160, hn160, originRegister, coordinateRegister, pointerRegister]
  exact (callerFrame_put s origin pointerRegister _ (Or.inl (by decide))).trans
    ((callerFrame_put s0 origin _ _ (Or.inr (Or.inr (by rw [ho]; exact slot_ge_origin _ _ _)))).trans
      ((callerFrame_put s1 origin coordinateRegister _ (Or.inl (by decide))).trans
        (callerFrame_logged s2 origin hh)))

theorem callerFrame_wordSet (s : Store) (origin address src : ℕ)
    (ho : s.val.indices originRegister = origin) :
    CallerFrame origin s.val (wordSet s address src).val := by
  let s0 := s.put pointerRegister (slot (s.val.indices originRegister) 0 address)
  let s1 := putWord s0 (slot (s.val.indices originRegister) 0 address) (s.val.words src)
  let s2 := s1.put coordinateRegister address
  have h160 : s.val.indices 160 = origin := ho
  have hh : s2.val.indices originRegister = origin := by
    simp [s2, s1, s0, putWord, h160, originRegister, coordinateRegister, pointerRegister]
  exact (callerFrame_put s origin pointerRegister _ (Or.inl (by decide))).trans
    ((callerFrame_word s0 origin _ _ (Or.inr (by rw [ho]; exact slot_ge_origin _ _ _))).trans
      ((callerFrame_put s1 origin coordinateRegister _ (Or.inl (by decide))).trans
        (callerFrame_logged s2 origin hh)))

end Maxwell.Cost.RealPrivate
