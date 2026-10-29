import Maxwell.Cost.RealSimulation.BasicInstructions

namespace Maxwell.Cost.RealSimulation

open Control

theorem Represents.put_tapeHead {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Represents L origin center bits source s.val)
    (t : ℕ) (ht : t < L.tapeCount) (head : ℤ) :
    Represents L origin center bits
      {source with tapes := Function.update source.tapes t {source.tapes t with head := head}}
      (s.put (L.tapeHead t) (centered center head)).val := by
  have hs : L.tapeHead t < origin := by
    have := h.origin_above_frame
    unfold Layout.tapeHead Layout.frameEnd at *
    omega
  have hc (j : ℕ) (hj : j < 256) : j ≠ L.tapeHead t := by
    unfold Layout.tapeHead
    omega
  have hb (bank coordinate : ℕ) : L.slot origin bank coordinate ≠ L.tapeHead t := by
    have := L.slot_ge_origin origin bank coordinate
    omega
  refine ⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.random_cursor⟩
  · simpa [hc _ (by decide : virtualPC < 256)] using h.pc
  · simpa [hc _ (by decide : addressLength < 256)] using h.address_length
  · simpa [hc _ (by decide : inputHead < 256)] using h.input_head
  · intro r hr
    have hn : L.bitRegister r ≠ L.tapeHead t := by
      unfold Layout.bitRegister Layout.tapeHead
      omega
    simpa [hn] using h.registers r hr
  · intro u hu
    by_cases he : u = t
    · subst u; simp
    · have hn : L.tapeHead u ≠ L.tapeHead t := by
        unfold Layout.tapeHead
        omega
      simpa [hn, Function.update_of_ne he] using h.tape_heads u hu
  · simpa [hc _ (by decide : workspaceOrigin < 256)] using h.origin_word
  · simpa [hc _ (by decide : bankStride < 256)] using h.stride_word
  · simpa [hc _ (by decide : headCenter < 256)] using h.center_word
  · simpa [hc _ (by decide : inputBase < 256)] using h.input_base
  · simpa [hc _ (by decide : inputLength < 256)] using h.input_length
  · simpa [hc _ (by decide : outputBase < 256)] using h.output_base
  · simpa [hc _ (by decide : outputLength < 256)] using h.output_length
  · intro j hj; simpa [hb] using h.input_cells j hj
  · intro j hj; simpa [hb] using h.output_cells j hj
  · intro j hj; simpa [hb] using h.stack_cells j hj
  · intro a; simpa [hb] using h.memory_cells a
  · intro u hu z hz
    by_cases he : u = t
    · subst u; simpa [hb] using h.tape_cells t ht z hz
    · simpa [hb, Function.update_of_ne he] using h.tape_cells u hu z hz

theorem Ready.put_tapeHead {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s)
    (t : ℕ) (ht : t < L.tapeCount) (head : ℤ) :
    Ready L origin center bits
      {source with tapes := Function.update source.tapes t {source.tapes t with head := head}}
      (s.put (L.tapeHead t) (centered center head)) := by
  have hn (j : ℕ) (hj : j < 256) : j ≠ L.tapeHead t := by
    unfold Layout.tapeHead
    omega
  refine ⟨h.toRepresents.put_tapeHead t ht head, ?_, ?_, ?_⟩
  · simpa [hn _ (by decide : zeroRegister < 256)] using h.zero
  · simpa [hn _ (by decide : oneRegister < 256)] using h.one
  · simpa [hn _ (by decide : activeRegister < 256)] using h.active

theorem Represents.put_tapeCell {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Represents L origin center bits source s.val)
    (t : ℕ) (ht : t < L.tapeCount) (b : Option Bool)
    (hh : -(center : ℤ) ≤ (source.tapes t).head) :
    Represents L origin center bits
      {source with tapes := Function.update source.tapes t ((source.tapes t).write b)}
      (s.put (L.slot origin (2 + t) (centered center (source.tapes t).head)) (symbol b)).val := by
  set p := L.slot origin (2 + t) (centered center (source.tapes t).head)
  have ho : L.frameEnd ≤ p := h.origin_above_frame.trans (L.slot_ge_origin origin _ _)
  have hsmall (j : ℕ) (hj : j < L.frameEnd) : j ≠ p := by omega
  have hc (j : ℕ) (hj : j < 256) : j ≠ p :=
    hsmall j (by unfold Layout.frameEnd; omega)
  have htb : 2 + t < L.stride := by unfold Layout.stride; omega
  have hb (bank x : ℕ) (hl : bank < L.stride) (hne : bank ≠ 2 + t) :
      L.slot origin bank x ≠ p :=
    L.slot_ne origin bank (2 + t) x _ hl htb hne
  refine ⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.random_cursor⟩
  · simpa [hc _ (by decide : virtualPC < 256)] using h.pc
  · simpa [hc _ (by decide : addressLength < 256)] using h.address_length
  · simpa [hc _ (by decide : inputHead < 256)] using h.input_head
  · intro r hr
    have hn := hsmall (L.bitRegister r) (by unfold Layout.bitRegister Layout.frameEnd; omega)
    simpa [hn] using h.registers r hr
  · intro u hu
    have hn := hsmall (L.tapeHead u) (by unfold Layout.tapeHead Layout.frameEnd; omega)
    by_cases he : u = t
    · subst u; simpa [hn, BitTape.write] using h.tape_heads t ht
    · simpa [hn, Function.update_of_ne he] using h.tape_heads u hu
  · simpa [hc _ (by decide : workspaceOrigin < 256)] using h.origin_word
  · simpa [hc _ (by decide : bankStride < 256)] using h.stride_word
  · simpa [hc _ (by decide : headCenter < 256)] using h.center_word
  · simpa [hc _ (by decide : inputBase < 256)] using h.input_base
  · simpa [hc _ (by decide : inputLength < 256)] using h.input_length
  · simpa [hc _ (by decide : outputBase < 256)] using h.output_base
  · simpa [hc _ (by decide : outputLength < 256)] using h.output_length
  · intro j hj
    have hn := hb L.inputBank j (by simp [Layout.inputBank, Layout.stride])
      (by unfold Layout.inputBank; omega)
    simpa [hn] using h.input_cells j hj
  · intro j hj
    have hn := hb L.outputBank j (by simp [Layout.outputBank, Layout.stride])
      (by unfold Layout.outputBank; omega)
    simpa [hn] using h.output_cells j hj
  · intro j hj
    have hn := hb 1 j (by simp [Layout.stride]) (by omega)
    simpa [hn] using h.stack_cells j hj
  · intro a
    have hn := hb 0 a L.stride_pos (by omega)
    simpa [hn] using h.memory_cells a
  · intro u hu z hz
    by_cases he : u = t
    · subst u
      by_cases hez : z = (source.tapes t).head
      · subst z; simp [BitTape.write, p]
      · have hn : L.slot origin (2 + t) (centered center z) ≠ p := by
          intro heq
          have heq' := ((L.slot_injective origin (2 + t) (2 + t) _ _ htb htb).mp heq).2
          have hz' := centered_cast center z hz
          have hh' := centered_cast center (source.tapes t).head hh
          omega
        simpa [hn, BitTape.write, Function.update_of_ne hez] using h.tape_cells t ht z hz
    · have hn := hb (2 + u) (centered center z) (by unfold Layout.stride; omega) (by omega)
      simpa [hn, Function.update_of_ne he] using h.tape_cells u hu z hz

theorem Ready.put_tapeCell {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s)
    (t : ℕ) (ht : t < L.tapeCount) (b : Option Bool)
    (hh : -(center : ℤ) ≤ (source.tapes t).head) :
    Ready L origin center bits
      {source with tapes := Function.update source.tapes t ((source.tapes t).write b)}
      (s.put (L.slot origin (2 + t) (centered center (source.tapes t).head)) (symbol b)) := by
  have ho : 256 ≤ L.slot origin (2 + t) (centered center (source.tapes t).head) := by
    have ho := h.origin_above_frame.trans
      (L.slot_ge_origin origin (2 + t) (centered center (source.tapes t).head))
    unfold Layout.frameEnd at ho
    omega
  have hn (j : ℕ) (hj : j < 256) :
      j ≠ L.slot origin (2 + t) (centered center (source.tapes t).head) := by omega
  refine ⟨h.toRepresents.put_tapeCell t ht b hh, ?_, ?_, ?_⟩
  · simpa [hn _ (by decide : zeroRegister < 256)] using h.zero
  · simpa [hn _ (by decide : oneRegister < 256)] using h.one
  · simpa [hn _ (by decide : activeRegister < 256)] using h.active

end Maxwell.Cost.RealSimulation
