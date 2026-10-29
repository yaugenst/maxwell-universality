import Maxwell.Cost.RealSimulation.AddressAccess

namespace Maxwell.Cost.RealSimulation

open Control

theorem Ready.emit {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s) (b : Bool) :
    Ready L origin center bits {source with output := b :: source.output}
      ((s.put (L.slot origin L.outputBank source.output.length) b.toNat).put outputLength
        (source.output.length + 1)) := by
  let p := L.slot origin L.outputBank source.output.length
  have ho : L.frameEnd ≤ p := h.origin_above_frame.trans (L.slot_ge_origin origin _ _)
  have hsmall (j : ℕ) (hj : j < L.frameEnd) : j ≠ p := by omega
  have hc (j : ℕ) (hj : j < 256) : j ≠ p :=
    hsmall j (by unfold Layout.frameEnd; omega)
  have hb (bank x : ℕ) (hl : bank < L.stride) (hne : bank ≠ L.outputBank) :
      L.slot origin bank x ≠ p :=
    L.slot_ne origin bank L.outputBank x source.output.length hl
      (by simp [Layout.outputBank, Layout.stride]) hne
  have hs (bank x : ℕ) : L.slot origin bank x ≠ outputLength := by
    have := L.slot_ge_origin origin bank x
    have hh := h.origin_above_frame
    unfold Layout.frameEnd outputLength at *
    omega
  have hrepr : Represents L origin center bits {source with output := b :: source.output}
      ((s.put p b.toNat).put outputLength (source.output.length + 1)).val := by
    refine ⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.random_cursor⟩
    · simpa only [Store.put_indices, ite_eq_right (by decide : virtualPC ≠ outputLength),
      ite_eq_right (hc _ (by decide : virtualPC < 256))] using h.pc
    · simpa only [Store.put_indices, ite_eq_right (by decide : addressLength ≠ outputLength),
      ite_eq_right (hc _ (by decide : addressLength < 256))] using h.address_length
    · simpa only [Store.put_indices, ite_eq_right (by decide : inputHead ≠ outputLength),
      ite_eq_right (hc _ (by decide : inputHead < 256))] using h.input_head
    · intro r hr
      have hn := hsmall (L.bitRegister r) (by unfold Layout.bitRegister Layout.frameEnd; omega)
      have hn' : L.bitRegister r ≠ outputLength := by unfold Layout.bitRegister outputLength; omega
      simpa [hn, hn'] using h.registers r hr
    · intro t ht
      have hn := hsmall (L.tapeHead t) (by unfold Layout.tapeHead Layout.frameEnd; omega)
      have hn' : L.tapeHead t ≠ outputLength := by unfold Layout.tapeHead outputLength; omega
      simpa [hn, hn'] using h.tape_heads t ht
    · simpa only [Store.put_indices, ite_eq_right (by decide : workspaceOrigin ≠ outputLength),
      ite_eq_right (hc _ (by decide : workspaceOrigin < 256))] using h.origin_word
    · simpa only [Store.put_indices, ite_eq_right (by decide : bankStride ≠ outputLength),
      ite_eq_right (hc _ (by decide : bankStride < 256))] using h.stride_word
    · simpa only [Store.put_indices, ite_eq_right (by decide : headCenter ≠ outputLength),
      ite_eq_right (hc _ (by decide : headCenter < 256))] using h.center_word
    · simpa only [Store.put_indices, ite_eq_right (by decide : inputBase ≠ outputLength),
      ite_eq_right (hc _ (by decide : inputBase < 256))] using h.input_base
    · simpa only [Store.put_indices, ite_eq_right (by decide : inputLength ≠ outputLength),
      ite_eq_right (hc _ (by decide : inputLength < 256))] using h.input_length
    · simpa only [Store.put_indices, ite_eq_right (by decide : outputBase ≠ outputLength),
      ite_eq_right (hc _ (by decide : outputBase < 256))] using h.output_base
    · simp
    · intro j hj
      have hn := hb L.inputBank j (by simp [Layout.inputBank, Layout.stride])
        (by simp [Layout.inputBank, Layout.outputBank])
      simpa [hn, hs] using h.input_cells j hj
    · intro j hj
      have hlen : j ≤ source.output.length := by simpa using hj
      by_cases he : j = source.output.length
      · subst j
        simp [p, hs, List.reverse_cons]
      · have hj' : j < source.output.length := by omega
        have hn : L.slot origin L.outputBank j ≠ p := by
          intro hh
          exact he ((L.slot_injective origin _ _ j source.output.length
            (by simp [Layout.outputBank, Layout.stride])
            (by simp [Layout.outputBank, Layout.stride])).mp hh).2
        have hr : j < source.output.reverse.length := by simpa using hj'
        simpa [hn, hs, List.reverse_cons, List.getElem?_append_left hr] using h.output_cells j hj'
    · intro j hj
      have hn := hb 1 j (by simp [Layout.stride]) (by unfold Layout.outputBank; omega)
      simpa [hn, hs] using h.stack_cells j hj
    · intro a
      have hn := hb 0 a L.stride_pos (by unfold Layout.outputBank; omega)
      simpa [hn, hs] using h.memory_cells a
    · intro t ht z hz
      have hn := hb (2 + t) (centered center z) (by unfold Layout.stride; omega)
        (by unfold Layout.outputBank; omega)
      simpa [hn, hs] using h.tape_cells t ht z hz
  refine ⟨hrepr, ?_, ?_, ?_⟩
  · change ((s.put p b.toNat).put outputLength (source.output.length + 1)).val.indices zeroRegister = 0
    simpa only [Store.put_indices, ite_eq_right (by decide : zeroRegister ≠ outputLength),
      ite_eq_right (hc _ (by decide : zeroRegister < 256))] using h.zero
  · change ((s.put p b.toNat).put outputLength (source.output.length + 1)).val.indices oneRegister = 1
    simpa only [Store.put_indices, ite_eq_right (by decide : oneRegister ≠ outputLength),
      ite_eq_right (hc _ (by decide : oneRegister < 256))] using h.one
  · change ((s.put p b.toNat).put outputLength (source.output.length + 1)).val.indices activeRegister = 1
    simpa only [Store.put_indices, ite_eq_right (by decide : activeRegister ≠ outputLength),
      ite_eq_right (hc _ (by decide : activeRegister < 256))] using h.active

theorem output_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (src : ℕ)
    (hs : src < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.output src))
        (2 * L.stride + 11) s t ∧
      Ready L origin center bits
        {source with pc := source.pc + 1, output := source.registers src :: source.output} t := by
  let p := L.slot origin L.outputBank source.output.length
  let s0 := s.put pointerRegister p
  have e0 : Executes input tape (bankPointer L L.outputBank outputLength)
      (2 * L.stride + 5) s s0 := by
    simpa [s0, p, h.origin_word, h.output_length] using
      bankPointer_executes input tape L s L.outputBank outputLength (by decide)
  have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  let s1 := s0.put p (source.registers src).toNat
  have e1 : Executes input tape (save pointerRegister (L.bitRegister src)) 2 s0 s1 := by
    have he := save_executes input tape s0 pointerRegister (L.bitRegister src)
    rw [show s0.val.indices pointerRegister = p by simp [s0], h0.registers src hs] at he
    exact he
  have ho : 256 ≤ p := by
    have ho := h.origin_above_frame.trans (L.slot_ge_origin origin L.outputBank source.output.length)
    unfold Layout.frameEnd at ho
    omega
  have hv : s1.val.indices outputLength = source.output.length := by
    simpa [s1, show outputLength ≠ p by unfold outputLength; omega] using h0.output_length
  have h1 : s1.val.indices oneRegister = 1 := by
    simpa [s1, show oneRegister ≠ p by unfold oneRegister; omega] using h0.one
  have e2 := add_executes input tape s1 outputLength outputLength oneRegister
  rw [hv, h1] at e2
  have h2 := h0.emit (source.registers src)
  have e3 := incrementPC_executes input tape _ h2
  refine ⟨_, ?_, e3.2⟩
  convert e0.seq (e1.seq (e2.seq e3.1)) using 1
  rfl

end Maxwell.Cost.RealSimulation
