import Maxwell.Cost.RealSimulation.AddressAccess
import Maxwell.Cost.RealSimulation.MemoryFrame

namespace Maxwell.Cost.RealSimulation

open Control

theorem readMemory_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst : ℕ)
    (hd : dst < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.readMemory dst))
        (7 * source.address.length + 2 * L.stride + 24) s t ∧
      Ready L origin center bits
        (source.setRegister dst (source.memory (addressValue source.address))) t := by
  obtain ⟨s0, e0, h0, hv⟩ := decodeStack_executes input tape s h
  let a := addressValue source.address
  let p := L.slot origin 0 a
  let s1 := s0.put pointerRegister p
  have e1 : Executes input tape (bankPointer L 0 3) (2 * L.stride + 5) s0 s1 := by
    simpa [s1, p, a, h0.origin_word, hv] using
      bankPointer_executes input tape L s0 0 3 (by decide)
  have h1 : Ready L origin center bits source s1 := h0.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have e2 : Executes input tape (load (L.bitRegister dst) pointerRegister) 2 s1
      (s1.put (L.bitRegister dst) (source.memory a).toNat) := by
    have he := load_executes input tape s1 (L.bitRegister dst) pointerRegister
    rw [show s1.val.indices pointerRegister = p by simp [s1]] at he
    rw [h1.memory_cells a] at he
    exact he
  have h2 := h1.put_register dst (source.memory a) hd
  have e3 := incrementPC_executes input tape _ h2
  refine ⟨_, ?_, e3.2⟩
  convert e0.seq (e1.seq (e2.seq e3.1)) using 1
  · rfl
  · omega

theorem writeMemory_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (src : ℕ)
    (hs : src < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.writeMemory src))
        (7 * source.address.length + 2 * L.stride + 24) s t ∧
      Ready L origin center bits
        {source with
          pc := source.pc + 1
          memory := Function.update source.memory (addressValue source.address) (source.registers src)} t := by
  obtain ⟨s0, e0, h0, hv⟩ := decodeStack_executes input tape s h
  let a := addressValue source.address
  let p := L.slot origin 0 a
  let s1 := s0.put pointerRegister p
  have e1 : Executes input tape (bankPointer L 0 3) (2 * L.stride + 5) s0 s1 := by
    simpa [s1, p, a, h0.origin_word, hv] using
      bankPointer_executes input tape L s0 0 3 (by decide)
  have h1 : Ready L origin center bits source s1 := h0.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have e2 : Executes input tape (save pointerRegister (L.bitRegister src)) 2 s1
      (s1.put p (source.registers src).toNat) := by
    simpa [show s1.val.indices pointerRegister = p by simp [s1], h1.registers src hs] using
      save_executes input tape s1 pointerRegister (L.bitRegister src)
  have h2 := h1.put_memory a (source.registers src)
  have e3 := incrementPC_executes input tape _ h2
  refine ⟨_, ?_, e3.2⟩
  convert e0.seq (e1.seq (e2.seq e3.1)) using 1
  · rfl
  · omega

theorem boundedInput_executes (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst coordinate : ℕ)
    (hd : dst < L.registerCount) (hc : coordinate ≠ pointerRegister) :
    ∃ cost t, cost ≤ 2 * L.stride + 8 ∧
      Executes input tape (boundedInput L dst coordinate) cost s t ∧
      Ready L origin center bits
        {source with
          registers := Function.update source.registers dst
            (bits[s.val.indices coordinate]?.getD false)} t := by
  by_cases hin : s.val.indices coordinate < bits.length
  · let a := s.val.indices coordinate
    let p := L.slot origin L.inputBank a
    let s0 := s.put pointerRegister p
    have e0 : Executes input tape (bankPointer L L.inputBank coordinate)
        (2 * L.stride + 5) s s0 := by
      simpa [s0, p, a, h.origin_word] using
        bankPointer_executes input tape L s L.inputBank coordinate hc
    have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
      (by decide) (by decide) (by decide)
    have e1 : Executes input tape (load (L.bitRegister dst) pointerRegister) 2 s0
        (s0.put (L.bitRegister dst) (bits[a]?.getD false).toNat) := by
      have he := load_executes input tape s0 (L.bitRegister dst) pointerRegister
      rw [show s0.val.indices pointerRegister = p by simp [s0]] at he
      rw [h0.input_cells a hin] at he
      exact he
    have htest : ¬ s.val.indices inputLength ≤ s.val.indices coordinate := by
      rw [h.input_length]
      omega
    refine ⟨2 * L.stride + 8, _, le_rfl, ?_, h0.put_register dst _ hd⟩
    convert Executes.no htest (e0.seq e1) using 1
    · rfl
    · omega
  · have hn : bits[s.val.indices coordinate]?.getD false = false := by
      rw [List.getElem?_eq_none (by omega)]
      rfl
    have htest : s.val.indices inputLength ≤ s.val.indices coordinate := by
      rw [h.input_length]
      omega
    refine ⟨3, s.put (L.bitRegister dst) 0, by omega,
      Executes.yes htest (literal_executes input tape s (L.bitRegister dst) 0), ?_⟩
    simpa [hn] using h.put_register dst false hd

theorem readInput_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst : ℕ)
    (hd : dst < L.registerCount) :
    ∃ cost t, cost ≤ 7 * source.address.length + 2 * L.stride + 25 ∧
      Executes input tape (instruction L Address.code (.readInput dst)) cost s t ∧
      Ready L origin center bits
        (source.setRegister dst (bits[addressValue source.address]?.getD false)) t := by
  obtain ⟨s0, e0, h0, hv⟩ := decodeStack_executes input tape s h
  obtain ⟨cost, s1, hb, e1, h1⟩ := boundedInput_executes input tape s0 h0 dst 3 hd (by decide)
  rw [hv] at h1
  have e2 := incrementPC_executes input tape s1 h1
  refine ⟨_, _, ?_, e0.seq (e1.seq e2.1), e2.2⟩
  omega

end Maxwell.Cost.RealSimulation
