import Maxwell.Cost.RealSimulation.MemoryInstructions

namespace Maxwell.Cost.RealSimulation

open Control

theorem Represents.put_inputHead {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Represents L origin center bits source s.val)
    (head : ℤ) : Represents L origin center bits {source with inputHead := head}
      (s.put inputHead (centered center head)).val := by
  have ho : 256 ≤ origin := by
    have := h.origin_above_frame
    unfold Layout.frameEnd at this
    omega
  have hn (bank coordinate : ℕ) : L.slot origin bank coordinate ≠ inputHead := by
    have := L.slot_ge_origin origin bank coordinate
    unfold inputHead
    omega
  refine ⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.random_cursor⟩
  · simpa [virtualPC, inputHead] using h.pc
  · simpa [addressLength, inputHead] using h.address_length
  · simp
  · intro r hr
    have hn : L.bitRegister r ≠ inputHead := by unfold Layout.bitRegister inputHead; omega
    simpa [hn] using h.registers r hr
  · intro t ht
    have hn : L.tapeHead t ≠ inputHead := by unfold Layout.tapeHead inputHead; omega
    simpa [hn] using h.tape_heads t ht
  · simpa [workspaceOrigin, inputHead] using h.origin_word
  · simpa [bankStride, inputHead] using h.stride_word
  · simpa [headCenter, inputHead] using h.center_word
  · simpa [inputBase, inputHead] using h.input_base
  · simpa [inputLength, inputHead] using h.input_length
  · simpa [outputBase, inputHead] using h.output_base
  · simpa [outputLength, inputHead] using h.output_length
  · intro j hj; simpa [hn] using h.input_cells j hj
  · intro j hj; simpa [hn] using h.output_cells j hj
  · intro j hj; simpa [hn] using h.stack_cells j hj
  · intro a; simpa [hn] using h.memory_cells a
  · intro t ht z hz; simpa [hn] using h.tape_cells t ht z hz

theorem Ready.put_inputHead {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s) (head : ℤ) :
    Ready L origin center bits {source with inputHead := head}
      (s.put inputHead (centered center head)) := by
  refine ⟨h.toRepresents.put_inputHead head, ?_, ?_, ?_⟩
  · simpa [zeroRegister, inputHead] using h.zero
  · simpa [oneRegister, inputHead] using h.one
  · simpa [activeRegister, inputHead] using h.active

theorem inputLeft_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (hh : -(center : ℤ) < source.inputHead) :
    ∃ t, Executes input tape (instruction L Address.code .inputLeft) 4 s t ∧
      Ready L origin center bits
        {source with pc := source.pc + 1, inputHead := source.inputHead - 1} t := by
  have he := subtract_executes input tape s inputHead inputHead oneRegister
  rw [h.input_head, h.one, ← centered_left center source.inputHead hh] at he
  have hp := incrementPC_executes input tape _ (h.put_inputHead (source.inputHead - 1))
  exact ⟨_, he.seq hp.1, hp.2⟩

theorem inputRight_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (hh : -(center : ℤ) ≤ source.inputHead) :
    ∃ t, Executes input tape (instruction L Address.code .inputRight) 4 s t ∧
      Ready L origin center bits
        {source with pc := source.pc + 1, inputHead := source.inputHead + 1} t := by
  have he := add_executes input tape s inputHead inputHead oneRegister
  rw [h.input_head, h.one, ← centered_right center source.inputHead hh] at he
  have hp := incrementPC_executes input tape _ (h.put_inputHead (source.inputHead + 1))
  exact ⟨_, he.seq hp.1, hp.2⟩

theorem readSequential_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst : ℕ)
    (hd : dst < L.registerCount) (hh : -(center : ℤ) ≤ source.inputHead) :
    ∃ cost t, cost ≤ 2 * L.stride + 13 ∧
      Executes input tape (instruction L Address.code (.readSequential dst)) cost s t ∧
      Ready L origin center bits (source.setRegister dst (inputBit bits source.inputHead)) t := by
  have hcast := centered_cast center source.inputHead hh
  by_cases hn : source.inputHead < 0
  · have htest : ¬ s.val.indices headCenter ≤ s.val.indices inputHead := by
      rw [h.center_word, h.input_head]
      omega
    have he := Executes.no (yes := .seq (subtract coordinateRegister inputHead headCenter)
      (boundedInput L dst coordinateRegister)) htest
      (literal_executes input tape s (L.bitRegister dst) 0)
    have hp := incrementPC_executes input tape _ (h.put_register dst false hd)
    refine ⟨5, _, by omega, he.seq hp.1, ?_⟩
    simpa [inputBit, hn, BitRAMState.setRegister] using hp.2
  · have htest : s.val.indices headCenter ≤ s.val.indices inputHead := by
      rw [h.center_word, h.input_head]
      omega
    have hv : s.val.indices inputHead - s.val.indices headCenter = source.inputHead.toNat := by
      rw [h.input_head, h.center_word]
      have := Int.toNat_of_nonneg (show 0 ≤ source.inputHead by omega)
      omega
    let s0 := s.put coordinateRegister source.inputHead.toNat
    have e0 : Executes input tape (subtract coordinateRegister inputHead headCenter) 2 s s0 := by
      simpa [hv, s0] using subtract_executes input tape s coordinateRegister inputHead headCenter
    have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
      (by decide) (by decide) (by decide)
    obtain ⟨cost, s1, hc, e1, h1⟩ := boundedInput_executes input tape s0 h0 dst coordinateRegister
      hd (by decide)
    have h1' : Ready L origin center bits
        {source with
          registers := Function.update source.registers dst
            (bits[source.inputHead.toNat]?.getD false)} s1 := by
      simpa [s0] using h1
    have e2 := incrementPC_executes input tape s1 h1'
    refine ⟨_, _, ?_, (Executes.yes htest (e0.seq e1)).seq e2.1, ?_⟩
    · omega
    · simpa [inputBit, hn, BitRAMState.setRegister] using e2.2

end Maxwell.Cost.RealSimulation
