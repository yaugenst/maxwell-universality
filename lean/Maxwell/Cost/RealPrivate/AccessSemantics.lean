import Maxwell.Cost.RealPrivate.CallerFrame

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem getIndex_correct (externalInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {source : RAMState} {written : List ℕ} (s : Store)
    (h : Represents origin source written s.val) (address dst : ℕ) (hd : dst < 6) :
    Executes externalInput tape (getIndex address dst) 6 s (indexed s address dst) ∧
    Represents origin source written (indexed s address dst).val ∧
    (indexed s address dst).val.indices dst = source.indices address ∧
    CallerFrame origin s.val (indexed s address dst).val := by
  have h0 := h.put_scratch pointerRegister
    (slot (s.val.indices originRegister) 0 address) (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
  have h1 := h0.put_scratch dst (s.val.indices (slot (s.val.indices originRegister) 0 address))
    (by unfold ProtectedIndex zeroRegister oneRegister; omega)
  refine ⟨getIndex_executes externalInput tape s address dst (by rw [h.origin_word]; exact h.high),
    h1, ?_, callerFrame_indexed s origin address dst (by omega)⟩
  simp [indexed, h.origin_word, h.indices]

theorem getWord_correct (externalInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {source : RAMState} {written : List ℕ} (s : Store)
    (h : Represents origin source written s.val) (address dst : ℕ) (hd : dst < 32) :
    Executes externalInput tape (getWord address dst) 6 s (worded s address dst) ∧
    Represents origin source written (worded s address dst).val ∧
    (worded s address dst).val.words dst = source.words address ∧
    CallerFrame origin s.val (worded s address dst).val := by
  have h0 := h.put_scratch pointerRegister
    (slot (s.val.indices originRegister) 0 address) (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
  have h1 := h0.word_scratch dst (s.val.words (slot (s.val.indices originRegister) 0 address))
    (by have := h.high; omega)
  refine ⟨getWord_executes externalInput tape s address dst, h1, ?_,
    callerFrame_worded s origin address dst hd⟩
  simp [worded, h.origin_word, h.words]

theorem incrementPC_correct (externalInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {source : RAMState} {written : List ℕ} (s : Store)
    (h : Represents origin source written s.val) :
    Executes externalInput tape incrementPC 2 s (s.put sourcePC (source.pc + 1)) ∧
    Represents origin {source with pc := source.pc + 1} written
      (s.put sourcePC (source.pc + 1)).val ∧
    CallerFrame origin s.val (s.put sourcePC (source.pc + 1)).val := by
  refine ⟨?_, h.put_pc _, callerFrame_put s origin sourcePC _ (Or.inr (Or.inl (by decide)))⟩
  simpa [incrementPC, h.pc, h.one] using add_executes externalInput tape s sourcePC sourcePC oneRegister

theorem readIndexInput_correct (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {B : InputBuffer} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val)
    (hi : Inputs L origin B sourceInput s.val) :
    ∃ cost t, cost ≤ 2 * L.indexInputStride + 6 ∧
      Executes externalInput tape (readIndexInput L) cost s t ∧
      Represents origin source written t.val ∧
      t.val.indices valueRegister = sourceInput.indices (s.val.indices coordinateRegister) ∧
      CallerFrame origin s.val t.val := by
  by_cases hb : B.indexLength ≤ s.val.indices coordinateRegister
  · refine ⟨3, s.put valueRegister 0, by omega, ?_,
      h.put_scratch valueRegister 0 (by simp [ProtectedIndex, valueRegister, zeroRegister, oneRegister]), ?_,
      callerFrame_put s origin valueRegister 0 (Or.inl (by decide))⟩
    · exact Executes.yes (left := indexInputLength) (right := coordinateRegister) (by rw [hi.index_length]; exact hb)
        (literal_executes externalInput tape s valueRegister 0)
    · simp [hi.index_outside _ hb]
  · let address := B.indexBase + L.indexInputStride * s.val.indices coordinateRegister
    let s0 := s.put pointerRegister address
    let t := s0.put valueRegister (sourceInput.indices (s.val.indices coordinateRegister))
    have hj : s.val.indices coordinateRegister < B.indexLength := by omega
    have ha : address ≠ pointerRegister := by have := hi.index_low; unfold address pointerRegister; omega
    have hp : Executes externalInput tape (inputPointer indexInputBase L.indexInputStride coordinateRegister)
        (2 * L.indexInputStride + 3) s s0 := by
      simpa [s0, address, hi.index_base] using
        inputPointer_executes externalInput tape s indexInputBase L.indexInputStride coordinateRegister (by decide)
    have hl : Executes externalInput tape (load valueRegister pointerRegister) 2 s0 t := by
      simpa [s0, t, ha, address, hi.index_cells _ hj] using
        load_executes externalInput tape s0 valueRegister pointerRegister
    have h0 := h.put_scratch pointerRegister address (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
    refine ⟨2 * L.indexInputStride + 6, t, le_rfl, ?_,
      h0.put_scratch valueRegister _ (by simp [ProtectedIndex, valueRegister, zeroRegister, oneRegister]), ?_,
      (callerFrame_put s origin pointerRegister _ (Or.inl (by decide))).trans
        (callerFrame_put s0 origin valueRegister _ (Or.inl (by decide)))⟩
    · have he := Executes.no (left := indexInputLength) (right := coordinateRegister)
        (yes := literal valueRegister 0) (no := Code.seq (inputPointer indexInputBase L.indexInputStride coordinateRegister)
        (load valueRegister pointerRegister)) (by rw [hi.index_length]; exact hb) (hp.seq hl)
      simpa only [readIndexInput,
        show 1 + (2 * L.indexInputStride + 3 + 2) = 2 * L.indexInputStride + 6 by omega] using he
    · simp [t]

theorem readRealInput_correct (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin : ℕ} {B : InputBuffer} {source : RAMState} {written : List ℕ}
    (s : Store) (h : Represents origin source written s.val)
    (hi : Inputs L origin B sourceInput s.val) :
    ∃ cost t, cost ≤ 2 * L.realInputStride + 6 ∧
      Executes externalInput tape (readRealInput L) cost s t ∧
      Represents origin source written t.val ∧
      t.val.words 0 = sourceInput.words (s.val.indices coordinateRegister) ∧
      CallerFrame origin s.val t.val := by
  by_cases hb : B.realLength ≤ s.val.indices coordinateRegister
  · refine ⟨3, putWord s 0 0, by omega, ?_,
      h.word_scratch 0 0 (by have := h.high; omega), ?_,
      callerFrame_word s origin 0 0 (Or.inl (by decide))⟩
    · have he : Executes externalInput tape (readRealInput L) 3 s (putWord s 0 (0 : ℚ)) :=
        Executes.yes (left := realInputLength) (right := coordinateRegister)
          (by rw [hi.real_length]; exact hb) (realLiteral_executes externalInput tape s 0 0)
      simpa only [Rat.cast_zero] using he
    · simp [hi.real_outside _ hb]
  · let address := B.realBase + L.realInputStride * s.val.indices coordinateRegister
    let s0 := s.put pointerRegister address
    let t := putWord s0 0 (sourceInput.words (s.val.indices coordinateRegister))
    have hj : s.val.indices coordinateRegister < B.realLength := by omega
    have hp : Executes externalInput tape (inputPointer realInputBase L.realInputStride coordinateRegister)
        (2 * L.realInputStride + 3) s s0 := by
      simpa [s0, address, hi.real_base] using
        inputPointer_executes externalInput tape s realInputBase L.realInputStride coordinateRegister (by decide)
    have hl : Executes externalInput tape (realLoad 0 pointerRegister) 2 s0 t := by
      simpa [s0, t, Store.put, address, hi.real_cells _ hj] using
        realLoad_executes externalInput tape s0 0 pointerRegister
    have h0 := h.put_scratch pointerRegister address (by simp [ProtectedIndex, pointerRegister, zeroRegister, oneRegister])
    refine ⟨2 * L.realInputStride + 6, t, le_rfl, ?_,
      h0.word_scratch 0 _ (by have := h.high; omega), ?_,
      (callerFrame_put s origin pointerRegister _ (Or.inl (by decide))).trans
        (callerFrame_word s0 origin 0 _ (Or.inl (by decide)))⟩
    · have he := Executes.no (left := realInputLength) (right := coordinateRegister)
        (yes := realLiteral 0 0) (no := Code.seq (inputPointer realInputBase L.realInputStride coordinateRegister)
        (realLoad 0 pointerRegister)) (by rw [hi.real_length]; exact hb) (hp.seq hl)
      simpa only [readRealInput,
        show 1 + (2 * L.realInputStride + 3 + 2) = 2 * L.realInputStride + 6 by omega] using he
    · simp [t]

end Maxwell.Cost.RealPrivate
