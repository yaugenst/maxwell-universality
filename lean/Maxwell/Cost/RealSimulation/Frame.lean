import Maxwell.Cost.RealSimulation.Primitives
import Maxwell.Cost.RealSimulation.Encoding

namespace Maxwell.Cost.RealSimulation

open Control

theorem Represents.congr {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s t : RAMState} (h : Represents L origin center bits source s)
    (hi : ∀ j, 20 ≤ j → t.indices j = s.indices j)
    (hc : t.randomCursor = s.randomCursor) : Represents L origin center bits source t := by
  have ho : 256 ≤ origin := by
    have := h.origin_above_frame
    unfold Layout.frameEnd at this
    omega
  have hs (bank coordinate : ℕ) : 20 ≤ L.slot origin bank coordinate :=
    (by omega : 20 ≤ origin).trans (L.slot_ge_origin origin bank coordinate)
  refine ⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc.trans h.random_cursor⟩
  · rw [hi virtualPC (by decide)]; exact h.pc
  · rw [hi addressLength (by decide)]; exact h.address_length
  · rw [hi inputHead (by decide)]; exact h.input_head
  · intro r hr; rw [hi _ (by unfold Layout.bitRegister; omega)]; exact h.registers r hr
  · intro t ht; rw [hi _ (by simp [Layout.tapeHead]; omega)]; exact h.tape_heads t ht
  · rw [hi workspaceOrigin (by decide)]; exact h.origin_word
  · rw [hi bankStride (by decide)]; exact h.stride_word
  · rw [hi headCenter (by decide)]; exact h.center_word
  · rw [hi inputBase (by decide)]; exact h.input_base
  · rw [hi inputLength (by decide)]; exact h.input_length
  · rw [hi outputBase (by decide)]; exact h.output_base
  · rw [hi outputLength (by decide)]; exact h.output_length
  · intro j hj; rw [hi _ (hs _ _)]; exact h.input_cells j hj
  · intro j hj; rw [hi _ (hs _ _)]; exact h.output_cells j hj
  · intro j hj; rw [hi _ (hs _ _)]; exact h.stack_cells j hj
  · intro a; rw [hi _ (hs _ _)]; exact h.memory_cells a
  · intro tape ht z hz; rw [hi _ (hs _ _)]; exact h.tape_cells tape ht z hz

theorem Represents.put_scratch {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Represents L origin center bits source s.val)
    (r v : ℕ) (hr : r < 20) : Represents L origin center bits source (s.put r v).val := by
  apply h.congr
  · intro j hj
    simp [show j ≠ r by omega]
  · rfl

theorem Represents.put_pc {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Represents L origin center bits source s.val)
    (pc : ℕ) : Represents L origin center bits {source with pc := pc}
      (s.put virtualPC pc).val := by
  have ho : 256 ≤ origin := by
    have := h.origin_above_frame
    unfold Layout.frameEnd at this
    omega
  have hn (bank coordinate : ℕ) : L.slot origin bank coordinate ≠ virtualPC := by
    have := L.slot_ge_origin origin bank coordinate
    unfold virtualPC
    omega
  refine ⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.random_cursor⟩
  · simp
  · simpa [addressLength, virtualPC] using h.address_length
  · simpa [inputHead, virtualPC] using h.input_head
  · intro r hr
    have hn : L.bitRegister r ≠ virtualPC := by unfold Layout.bitRegister virtualPC; omega
    simpa [hn] using h.registers r hr
  · intro t ht
    have hn : L.tapeHead t ≠ virtualPC := by unfold Layout.tapeHead virtualPC; omega
    simpa [hn] using h.tape_heads t ht
  · simpa [workspaceOrigin, virtualPC] using h.origin_word
  · simpa [bankStride, virtualPC] using h.stride_word
  · simpa [headCenter, virtualPC] using h.center_word
  · simpa [inputBase, virtualPC] using h.input_base
  · simpa [inputLength, virtualPC] using h.input_length
  · simpa [outputBase, virtualPC] using h.output_base
  · simpa [outputLength, virtualPC] using h.output_length
  · intro j hj; simpa [hn] using h.input_cells j hj
  · intro j hj; simpa [hn] using h.output_cells j hj
  · intro j hj; simpa [hn] using h.stack_cells j hj
  · intro a; simpa [hn] using h.memory_cells a
  · intro t ht z hz; simpa [hn] using h.tape_cells t ht z hz

theorem Represents.put_register {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Represents L origin center bits source s.val)
    (r : ℕ) (b : Bool) (hr : r < L.registerCount) :
    Represents L origin center bits
      {source with registers := Function.update source.registers r b}
      (s.put (L.bitRegister r) b.toNat).val := by
  have hro : L.bitRegister r < origin := by
    have := h.origin_above_frame
    unfold Layout.frameEnd Layout.bitRegister at *
    omega
  have hn (bank coordinate : ℕ) : L.slot origin bank coordinate ≠ L.bitRegister r := by
    have := L.slot_ge_origin origin bank coordinate
    omega
  have hsmall (j : ℕ) (hj : j < 256) : j ≠ L.bitRegister r := by
    unfold Layout.bitRegister
    omega
  refine ⟨h.origin_above_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.random_cursor⟩
  · simpa [hsmall _ (by decide : virtualPC < 256)] using h.pc
  · simpa [hsmall _ (by decide : addressLength < 256)] using h.address_length
  · simpa [hsmall _ (by decide : inputHead < 256)] using h.input_head
  · intro j hj
    by_cases he : j = r
    · subst j; simp
    · have hne : L.bitRegister j ≠ L.bitRegister r := by simpa [Layout.bitRegister] using he
      simpa [hne, Function.update_of_ne he] using h.registers j hj
  · intro t ht
    have hne : L.tapeHead t ≠ L.bitRegister r := by
      unfold Layout.tapeHead Layout.bitRegister
      omega
    simpa [hne] using h.tape_heads t ht
  · simpa [hsmall _ (by decide : workspaceOrigin < 256)] using h.origin_word
  · simpa [hsmall _ (by decide : bankStride < 256)] using h.stride_word
  · simpa [hsmall _ (by decide : headCenter < 256)] using h.center_word
  · simpa [hsmall _ (by decide : inputBase < 256)] using h.input_base
  · simpa [hsmall _ (by decide : inputLength < 256)] using h.input_length
  · simpa [hsmall _ (by decide : outputBase < 256)] using h.output_base
  · simpa [hsmall _ (by decide : outputLength < 256)] using h.output_length
  · intro j hj; simpa [hn] using h.input_cells j hj
  · intro j hj; simpa [hn] using h.output_cells j hj
  · intro j hj; simpa [hn] using h.stack_cells j hj
  · intro a; simpa [hn] using h.memory_cells a
  · intro t ht z hz; simpa [hn] using h.tape_cells t ht z hz

end Maxwell.Cost.RealSimulation
