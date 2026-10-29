import Maxwell.Cost.RealSimulation.BasicInstructions

namespace Maxwell.Cost.RealSimulation

open Control

theorem xor_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst left right : ℕ)
    (hd : dst < L.registerCount) (hl : left < L.registerCount) (hr : right < L.registerCount) :
    ∃ cost t, cost ≤ 8 ∧
      Executes input tape (instruction L Address.code (.bitXor dst left right)) cost s t ∧
      Ready L origin center bits
        (source.setRegister dst (xor (source.registers left) (source.registers right))) t := by
  let v := (source.registers left).toNat + (source.registers right).toNat
  let s0 := s.put valueRegister v
  have e0 : Executes input tape (add valueRegister (L.bitRegister left) (L.bitRegister right))
      2 s s0 := by
    simpa [s0, v, h.registers left hl, h.registers right hr] using
      add_executes input tape s valueRegister (L.bitRegister left) (L.bitRegister right)
  have h0 : Ready L origin center bits source s0 := h.put_scratch _ _ (by decide)
    (by decide) (by decide) (by decide)
  have hv : s0.val.indices valueRegister = v := by simp [s0]
  let b := xor (source.registers left) (source.registers right)
  have he : ∃ cost, cost ≤ 4 ∧ Executes input tape
      (.branch valueRegister oneRegister
        (.branch oneRegister valueRegister (literal (L.bitRegister dst) 1)
          (literal (L.bitRegister dst) 0)) (literal (L.bitRegister dst) 0))
      cost s0 (s0.put (L.bitRegister dst) b.toNat) := by
    cases ha : source.registers left <;> cases hb : source.registers right
    · refine ⟨4, by decide, ?_⟩
      apply Executes.yes (cost := 3) (by simp [hv, h0.one, v, ha, hb])
      apply Executes.no (cost := 2) (by simp [hv, h0.one, v, ha, hb])
      simpa [b, ha, hb] using literal_executes input tape s0 (L.bitRegister dst) 0
    · refine ⟨4, by decide, ?_⟩
      apply Executes.yes (cost := 3) (by simp [hv, h0.one, v, ha, hb])
      apply Executes.yes (cost := 2) (by simp [hv, h0.one, v, ha, hb])
      simpa [b, ha, hb] using literal_executes input tape s0 (L.bitRegister dst) 1
    · refine ⟨4, by decide, ?_⟩
      apply Executes.yes (cost := 3) (by simp [hv, h0.one, v, ha, hb])
      apply Executes.yes (cost := 2) (by simp [hv, h0.one, v, ha, hb])
      simpa [b, ha, hb] using literal_executes input tape s0 (L.bitRegister dst) 1
    · refine ⟨3, by decide, ?_⟩
      apply Executes.no (cost := 2) (by simp [hv, h0.one, v, ha, hb])
      simpa [b, ha, hb] using literal_executes input tape s0 (L.bitRegister dst) 0
  obtain ⟨cost, hc, e1⟩ := he
  have e2 := incrementPC_executes input tape _ (h0.put_register dst b hd)
  exact ⟨_, _, by omega, e0.seq (e1.seq e2.1), e2.2⟩

def drawn (s : Store) (dst : ℕ) (b : Bool) : Store :=
  ⟨{s.val with
    pc := 0
    words := Function.update (Function.update s.val.words 0 (if b then 1 else 0)) 1 0
    indices := Function.update s.val.indices dst b.toNat
    randomCursor := s.val.randomCursor + 1}, rfl⟩

theorem drawBit_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) (dst : ℕ) :
    Executes input tape (drawBit dst) 6 s (drawn s dst (tape s.val.randomCursor)) := by
  let t : RAMState := {(drawn s dst (tape s.val.randomCursor)).val with pc := 7}
  have he : Steps ((⟨[
      .randomBit 0, .literal 1 0, .branchLE 0 1 3 5,
      .indexLiteral dst 0, .jump 7,
      .indexLiteral dst 1, .jump 7, .halt]⟩ : Machine).next input tape) 5 s.val t := by
    apply advance_steps
    cases hb : tape s.val.randomCursor <;>
      norm_num [advance, Machine.next, s.property, hb, RAMState.setWord,
        RAMState.setIndex, drawn, t]
  exact Executes.call _ s t 5 he rfl

theorem Ready.after_draw {L : Layout} {origin center : ℕ} {bits : List Bool}
    {source : BitRAMState} {s : Store} (h : Ready L origin center bits source s)
    (dst : ℕ) (b : Bool) (hd : dst < L.registerCount) :
    Ready L origin center bits
      {source with
        registers := Function.update source.registers dst b
        randomCursor := source.randomCursor + 1}
      (drawn s (L.bitRegister dst) b) := by
  have hr := h.put_register dst b hd
  have hrepr : Represents L origin center bits
      {source with
        registers := Function.update source.registers dst b
        randomCursor := source.randomCursor + 1}
      (drawn s (L.bitRegister dst) b).val := by
    refine ⟨hr.origin_above_frame, hr.pc, hr.address_length, hr.input_head,
      hr.registers, hr.tape_heads, hr.origin_word, hr.stride_word, hr.center_word,
      hr.input_base, hr.input_length, hr.output_base, hr.output_length,
      hr.input_cells, hr.output_cells, hr.stack_cells, hr.memory_cells,
      hr.tape_cells, ?_⟩
    exact congrArg (fun n => n + 1) h.random_cursor
  exact ⟨hrepr, hr.zero, hr.one, hr.active⟩

theorem randomBit_instruction (input : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (s : Store) (h : Ready L origin center bits source s) (dst : ℕ)
    (hd : dst < L.registerCount) :
    ∃ t, Executes input tape (instruction L Address.code (.randomBit dst)) 8 s t ∧
      Ready L origin center bits
        {source.setRegister dst (tape source.randomCursor) with
          randomCursor := source.randomCursor + 1} t := by
  have he := drawBit_executes input tape s (L.bitRegister dst)
  rw [h.random_cursor] at he
  have hp := incrementPC_executes input tape _ (h.after_draw dst (tape source.randomCursor) hd)
  exact ⟨_, he.seq hp.1, hp.2⟩

end Maxwell.Cost.RealSimulation
