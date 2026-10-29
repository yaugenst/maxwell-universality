import Maxwell.Cost.RealSimulation.BasicInstructions

namespace Maxwell.Cost.RealSimulation

open Control

theorem Represents.put_memory {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Represents L origin center bits source s.val)
    (a : ℕ) (b : Bool) :
    Represents L origin center bits {source with memory := Function.update source.memory a b}
      (s.put (L.slot origin 0 a) b.toNat).val := by
  have ho : L.frameEnd ≤ L.slot origin 0 a :=
    h.origin_above_frame.trans (L.slot_ge_origin origin 0 a)
  have hsmall (j : ℕ) (hj : j < L.frameEnd) : j ≠ L.slot origin 0 a := by omega
  have hc (j : ℕ) (hj : j < 256) : j ≠ L.slot origin 0 a :=
    hsmall j (by unfold Layout.frameEnd; omega)
  have hb (bank x : ℕ) (hp : 0 < bank) (hl : bank < L.stride) :
      L.slot origin bank x ≠ L.slot origin 0 a :=
    L.slot_ne origin bank 0 x a hl L.stride_pos (by omega)
  refine ⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.random_cursor⟩
  · simpa [hc _ (by decide : virtualPC < 256)] using h.pc
  · simpa [hc _ (by decide : addressLength < 256)] using h.address_length
  · simpa [hc _ (by decide : inputHead < 256)] using h.input_head
  · intro r hr
    have hn := hsmall (L.bitRegister r) (by unfold Layout.bitRegister Layout.frameEnd; omega)
    simpa [hn] using h.registers r hr
  · intro t ht
    have hn := hsmall (L.tapeHead t) (by unfold Layout.tapeHead Layout.frameEnd; omega)
    simpa [hn] using h.tape_heads t ht
  · simpa [hc _ (by decide : workspaceOrigin < 256)] using h.origin_word
  · simpa [hc _ (by decide : bankStride < 256)] using h.stride_word
  · simpa [hc _ (by decide : headCenter < 256)] using h.center_word
  · simpa [hc _ (by decide : inputBase < 256)] using h.input_base
  · simpa [hc _ (by decide : inputLength < 256)] using h.input_length
  · simpa [hc _ (by decide : outputBase < 256)] using h.output_base
  · simpa [hc _ (by decide : outputLength < 256)] using h.output_length
  · intro j hj
    have hn := hb L.inputBank j (by simp [Layout.inputBank])
      (by simp [Layout.inputBank, Layout.stride])
    simpa [hn] using h.input_cells j hj
  · intro j hj
    have hn := hb L.outputBank j (by simp [Layout.outputBank])
      (by simp [Layout.outputBank, Layout.stride])
    simpa [hn] using h.output_cells j hj
  · intro j hj
    have hn := hb 1 j (by decide) (by simp [Layout.stride])
    simpa [hn] using h.stack_cells j hj
  · intro x
    by_cases he : x = a
    · subst x; simp
    · have hn : L.slot origin 0 x ≠ L.slot origin 0 a := by
        intro hx
        exact he ((L.slot_injective origin 0 0 x a L.stride_pos L.stride_pos).mp hx).2
      simpa [hn, Function.update_of_ne he] using h.memory_cells x
  · intro t ht z hz
    have hn := hb (2 + t) (centered center z) (by omega)
      (by unfold Layout.stride; omega)
    simpa [hn] using h.tape_cells t ht z hz

theorem Ready.put_memory {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s)
    (a : ℕ) (b : Bool) :
    Ready L origin center bits {source with memory := Function.update source.memory a b}
      (s.put (L.slot origin 0 a) b.toNat) := by
  have ho : 256 ≤ L.slot origin 0 a := by
    have ho := h.origin_above_frame.trans (L.slot_ge_origin origin 0 a)
    unfold Layout.frameEnd at ho
    omega
  have hn (j : ℕ) (hj : j < 256) : j ≠ L.slot origin 0 a := by omega
  refine ⟨h.toRepresents.put_memory a b, ?_, ?_, ?_⟩
  · simpa [hn _ (by decide : zeroRegister < 256)] using h.zero
  · simpa [hn _ (by decide : oneRegister < 256)] using h.one
  · simpa [hn _ (by decide : activeRegister < 256)] using h.active

end Maxwell.Cost.RealSimulation
