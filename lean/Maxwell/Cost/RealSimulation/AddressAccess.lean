import Maxwell.Cost.RealSimulation.BasicInstructions

namespace Maxwell.Cost.RealSimulation

open Control

theorem bankPointer_executes (input : RAMInput) (tape : ℕ → Bool)
    (L : Layout) (s : Store) (bank coordinate : ℕ) (hc : coordinate ≠ pointerRegister) :
    Executes input tape (bankPointer L bank coordinate) (2 * L.stride + 5) s
      (s.put pointerRegister (L.slot (s.val.indices workspaceOrigin) bank
        (s.val.indices coordinate))) := by
  have h1 := literal_executes input tape s pointerRegister bank
  have h2 := add_executes input tape (s.put pointerRegister bank)
    pointerRegister pointerRegister workspaceOrigin
  have h3 := repeatAdd_executes input tape
    ((s.put pointerRegister bank).put pointerRegister
      ((s.put pointerRegister bank).val.indices pointerRegister +
        (s.put pointerRegister bank).val.indices workspaceOrigin))
    pointerRegister coordinate L.stride hc
  have h := h1.seq (h2.seq h3)
  have hc' : coordinate ≠ 14 := hc
  convert h using 1 <;>
    simp [bankPointer, sequence, Layout.slot, pointerRegister, workspaceOrigin,
      hc', Nat.add_comm, Nat.add_left_comm]; omega

theorem Ready.address_frame {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s t : Store} (h : Ready L origin center bits source s)
    (hf : Address.Frame s.val t.val) : Ready L origin center bits source t := by
  refine ⟨h.toRepresents.congr (fun j hj => hf.indices j (Or.inr (by omega)))
      hf.randomCursor, ?_, ?_, ?_⟩
  · rw [hf.indices zeroRegister (Or.inr (by decide))]; exact h.zero
  · rw [hf.indices oneRegister (Or.inr (by decide))]; exact h.one
  · rw [hf.indices activeRegister (Or.inr (by decide))]; exact h.active

theorem decodeStack_executes (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) :
    ∃ t, Executes input tape (decodeStack Address.code)
        (7 * source.address.length + 15) s t ∧
      Ready L origin center bits source t ∧ t.val.indices 3 = addressValue source.address := by
  let s0 := s.put 0 source.address.length
  let s1 := s0.put 1 origin
  let s2 := s1.put 1 (origin + 1)
  let s3 := s2.put 2 L.stride
  have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have h1 : Ready L origin center bits source s1 := h0.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have h2 : Ready L origin center bits source s2 := h1.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have h3 : Ready L origin center bits source s3 := h2.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have ho : 9 ≤ origin + 1 := by
    have := h.origin_above_frame
    unfold Layout.frameEnd at this
    omega
  have hc : ∀ j < source.address.length,
      s3.val.indices (origin + 1 + L.stride * j) =
        (source.address.reverse[j]?.getD false).toNat := by
    intro j hj
    simpa [Layout.slot, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      h3.stack_cells j hj
  obtain ⟨t, he, hv, _, _, hf⟩ := Address.executes input tape source.address
    (origin + 1) L.stride ho s3 (by simp [s3, s2, s1, s0])
    (by simp [s3, s2]) (by simp [s3]) hc
  have e0 : Executes input tape (copy 0 addressLength) 2 s s0 := by
    simpa [s0, h.address_length] using copy_executes input tape s 0 addressLength
  have e1 : Executes input tape (copy 1 workspaceOrigin) 2 s0 s1 := by
    simpa [s1, h0.origin_word] using copy_executes input tape s0 1 workspaceOrigin
  have e2 : Executes input tape (add 1 1 oneRegister) 2 s1 s2 := by
    have he := add_executes input tape s1 1 1 oneRegister
    rw [show s1.val.indices 1 = origin by simp [s1], h1.one] at he
    exact he
  have e3 : Executes input tape (copy 2 bankStride) 2 s2 s3 := by
    simpa [s3, h2.stride_word] using copy_executes input tape s2 2 bankStride
  refine ⟨t, ?_, h3.address_frame hf, hv⟩
  have hall := e0.seq (e1.seq (e2.seq (e3.seq he)))
  convert hall using 1
  · rfl
  · omega

end Maxwell.Cost.RealSimulation
