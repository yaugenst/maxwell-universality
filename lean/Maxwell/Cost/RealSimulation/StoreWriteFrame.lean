import Maxwell.Cost.RealSimulation.WriteFrame

namespace Maxwell.Cost.RealSimulation
open Control

theorem writeMemory_instruction_framed (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (src : ℕ)
    (hs : src < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.writeMemory src))
        (7 * source.address.length + 2 * L.stride + 24) s t ∧
      Ready L origin center bits
        {source with
          pc := source.pc + 1
          memory := Function.update source.memory (addressValue source.address) (source.registers src)} t ∧
      WriteFrame L s.val t.val := by
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
  have hf := ((local_decodeStack L).frame e0).put_scalar pointerRegister p (scalar_small L _ (by decide))
  have hf := hf.put_small p (source.registers src).toNat (by cases source.registers src <;> decide)
  have hf := hf.put_scalar virtualPC (source.pc + 1) (scalar_pc L)
  refine ⟨_, ?_, e3.2, hf⟩
  convert e0.seq (e1.seq (e2.seq e3.1)) using 1
  · rfl
  · omega

theorem eraseTape_instruction_framed (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (t : ℕ)
    (ht : t < L.tapeCount) (hh : -(center : ℤ) ≤ (source.tapes t).head) :
    ∃ u, Executes input tape (instruction L Address.code (.eraseTape t))
        (2 * L.stride + 9) s u ∧
      Ready L origin center bits (source.setTape t ((source.tapes t).write none)) u ∧
      WriteFrame L s.val u.val := by
  let p := L.slot origin (2 + t) (centered center (source.tapes t).head)
  let s0 := s.put pointerRegister p
  have e0 : Executes input tape (bankPointer L (2 + t) (L.tapeHead t))
      (2 * L.stride + 5) s s0 := by
    simpa only [h.origin_word, h.tape_heads t ht] using
      bankPointer_executes input tape L s (2 + t) (L.tapeHead t)
        (by unfold Layout.tapeHead pointerRegister; omega)
  have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have e1 : Executes input tape (save pointerRegister zeroRegister) 2 s0 (s0.put p 0) := by
    simpa only [show s0.val.indices pointerRegister = p by simp [s0], h0.zero] using
      save_executes input tape s0 pointerRegister zeroRegister
  have e2 := incrementPC_executes input tape _ (h0.put_tapeCell t ht none hh)
  have hf := (WriteFrame.refl L s.val).put_scalar pointerRegister p (scalar_small L _ (by decide))
  have hf := hf.put_small p 0 (by decide)
  have hf := hf.put_scalar virtualPC (source.pc + 1) (scalar_pc L)
  refine ⟨_, ?_, e2.2, hf⟩
  convert e0.seq (e1.seq e2.1) using 1
  rfl

theorem writeTape_instruction_framed (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (t src : ℕ)
    (ht : t < L.tapeCount) (hs : src < L.registerCount)
    (hh : -(center : ℤ) ≤ (source.tapes t).head) :
    ∃ u, Executes input tape (instruction L Address.code (.writeTape t src))
        (2 * L.stride + 11) s u ∧
      Ready L origin center bits
        (source.setTape t ((source.tapes t).write (some (source.registers src)))) u ∧
      WriteFrame L s.val u.val := by
  let b := source.registers src
  let s0 := s.put valueRegister (symbol (some b))
  have e0 : Executes input tape (add valueRegister (L.bitRegister src) oneRegister) 2 s s0 := by
    simpa only [s0, b, symbol_some, h.registers src hs, h.one] using
      add_executes input tape s valueRegister (L.bitRegister src) oneRegister
  have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  let p := L.slot origin (2 + t) (centered center (source.tapes t).head)
  let s1 := s0.put pointerRegister p
  have e1 : Executes input tape (bankPointer L (2 + t) (L.tapeHead t))
      (2 * L.stride + 5) s0 s1 := by
    simpa only [h0.origin_word, h0.tape_heads t ht] using
      bankPointer_executes input tape L s0 (2 + t) (L.tapeHead t)
        (by unfold Layout.tapeHead pointerRegister; omega)
  have h1 : Ready L origin center bits source s1 := h0.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have e2 : Executes input tape (save pointerRegister valueRegister) 2 s1
      (s1.put p (symbol (some b))) := by
    simpa only [show s1.val.indices pointerRegister = p by simp [s1],
      show s1.val.indices valueRegister = symbol (some b) by
        simp [s1, s0, valueRegister, pointerRegister]] using
      save_executes input tape s1 pointerRegister valueRegister
  have e3 := incrementPC_executes input tape _ (h1.put_tapeCell t ht (some b) hh)
  have hf := (WriteFrame.refl L s.val).put_scalar valueRegister (symbol (some b)) (scalar_small L _ (by decide))
  have hf := hf.put_scalar pointerRegister p (scalar_small L _ (by decide))
  have hf := hf.put_small p (symbol (some b)) (by cases b <;> decide)
  have hf := hf.put_scalar virtualPC (source.pc + 1) (scalar_pc L)
  refine ⟨_, ?_, e3.2, hf⟩
  convert e0.seq (e1.seq (e2.seq e3.1)) using 1
  · rfl
  · omega

theorem addressPush_instruction_framed (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (src : ℕ)
    (hs : src < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.addressPush src))
        (2 * L.stride + 11) s t ∧
      Ready L origin center bits
        {source with pc := source.pc + 1, address := source.registers src :: source.address} t ∧
      WriteFrame L s.val t.val := by
  let bankAddress := L.slot origin 1 source.address.length
  let p := s.put pointerRegister bankAddress
  have ep : Executes input tape (bankPointer L 1 addressLength) (2 * L.stride + 5) s p := by
    simpa only [h.origin_word, h.address_length] using
      bankPointer_executes input tape L s 1 addressLength (by decide)
  have hp : Ready L origin center bits source p := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  let w := p.put bankAddress (source.registers src).toNat
  have ew : Executes input tape (save pointerRegister (L.bitRegister src)) 2 p w := by
    simpa only [show p.val.indices pointerRegister = bankAddress by simp [p], hp.registers src hs] using
      save_executes input tape p pointerRegister (L.bitRegister src)
  have hat : 256 ≤ bankAddress := by
    have := h.origin_above_frame
    have := L.slot_ge_origin origin 1 source.address.length
    unfold Layout.frameEnd at *
    omega
  have el : Executes input tape (add addressLength addressLength oneRegister) 2 w
      (w.put addressLength (source.address.length + 1)) := by
    simpa only [w, Store.put_indices, show addressLength ≠ bankAddress by unfold addressLength; omega,
      show oneRegister ≠ bankAddress by unfold oneRegister; omega, ↓reduceIte,
      hp.address_length, hp.one] using add_executes input tape w addressLength addressLength oneRegister
  have hpush : Ready L origin center bits {source with address := source.registers src :: source.address}
      (w.put addressLength (source.address.length + 1)) := hp.push_address (source.registers src)
  have efinish := incrementPC_executes input tape _ hpush
  have hf := (WriteFrame.refl L s.val).put_scalar pointerRegister bankAddress (scalar_small L _ (by decide))
  have hf := hf.put_small bankAddress (source.registers src).toNat (by cases source.registers src <;> decide)
  have hf := hf.put_scalar addressLength (source.address.length + 1) (scalar_length L)
  have hf := hf.put_scalar virtualPC (source.pc + 1) (scalar_pc L)
  refine ⟨_, ?_, efinish.2, hf⟩
  have e := ep.seq (ew.seq (el.seq efinish.1))
  convert e using 1
  rfl

theorem output_instruction_framed (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (src : ℕ)
    (hs : src < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.output src))
        (2 * L.stride + 11) s t ∧
      Ready L origin center bits
        {source with pc := source.pc + 1, output := source.registers src :: source.output} t ∧
      WriteFrame L s.val t.val := by
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
  have hf := (WriteFrame.refl L s.val).put_scalar pointerRegister p (scalar_small L _ (by decide))
  have hf := hf.put_small p (source.registers src).toNat (by cases source.registers src <;> decide)
  have hf := hf.put_scalar outputLength (source.output.length + 1) (scalar_outputLength L)
  have hf := hf.put_scalar virtualPC (source.pc + 1) (scalar_pc L)
  refine ⟨_, ?_, e3.2, hf⟩
  convert e0.seq (e1.seq (e2.seq e3.1)) using 1
  rfl

theorem instruction_frame (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (op : BitRAMInstruction) (fit : Fits L op) (s t : Store)
    (h : Ready L origin center bits source s)
    (heads : ∀ k < L.tapeCount, -(center : ℤ) ≤ (source.tapes k).head)
    {cost : ℕ} (execution : Executes input tape (instruction L Address.code op) cost s t) :
    WriteFrame L s.val t.val := by
  by_cases hs : HasBankStore op
  · cases op <;> simp only [HasBankStore] at hs
    all_goals simp only [Fits, registerCap, tapeCap] at fit
    case writeTape k r =>
      obtain ⟨u, he, _, hf⟩ := writeTape_instruction_framed input tape s h k r
        (by omega) (by omega) (heads k (by omega))
      rw [execution.same_store he]
      exact hf
    case eraseTape k =>
      obtain ⟨u, he, _, hf⟩ := eraseTape_instruction_framed input tape s h k
        (by omega) (heads k (by omega))
      rw [execution.same_store he]
      exact hf
    case addressPush r =>
      obtain ⟨u, he, _, hf⟩ := addressPush_instruction_framed input tape s h r (by omega)
      rw [execution.same_store he]
      exact hf
    case writeMemory r =>
      obtain ⟨u, he, _, hf⟩ := writeMemory_instruction_framed input tape s h r (by omega)
      rw [execution.same_store he]
      exact hf
    case output r =>
      obtain ⟨u, he, _, hf⟩ := output_instruction_framed input tape s h r (by omega)
      rw [execution.same_store he]
      exact hf
  · exact (instruction_local L op fit hs).frame execution

end Maxwell.Cost.RealSimulation
