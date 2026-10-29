import Maxwell.Cost.ScanForward
import Maxwell.Cost.TrimShifted
import Maxwell.Cost.Scan
import Maxwell.Cost.Blocks

/-! One fixed finite routine converts an arithmetic word at its first cell
to the exact canonical codec word, at the same origin. Traversal, erasure,
return jumps, and final rewind are all included in the bound. -/

namespace Maxwell.Cost.NormalizeWord

def program (workTape : ℕ) : BitRAM := ⟨
  ((ScanForward.program workTape).code.map (BitRAMInstruction.relocate 0 5)) ++
  ((TapeOps.trim workTape).code.map (BitRAMInstruction.relocate 5 14)) ++
  ((Rewind.program workTape).code.map (BitRAMInstruction.relocate 14 19)) ++
  [.halt]⟩

theorem contains_forward (workTape : ℕ) :
    (program workTape).Contains (ScanForward.program workTape) 0 5 := by
  intro i
  fin_cases i <;> rfl

theorem contains_trim (workTape : ℕ) :
    (program workTape).Contains (TapeOps.trim workTape) 5 14 := by
  intro i
  fin_cases i <;> rfl

theorem contains_rewind (workTape : ℕ) :
    (program workTape).Contains (Rewind.program workTape) 14 19 := by
  intro i
  fin_cases i <;> rfl

def Frame (workTape : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ workTape → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.trans {workTape : ℕ} {s t u : BitRAMState}
    (h : Frame workTape s t) (k : Frame workTape t u) : Frame workTape s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hne => (kt i hne).trans (ht i hne),
    fun i h24 h25 h26 h27 => (kg i h24 h25 h26 h27).trans (hg i h24 h25 h26 h27)⟩

theorem frame_of_tapeOps {workTape : ℕ} {s t : BitRAMState}
    (h : TapeOps.Frame workTape workTape s t) : Frame workTape s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hne => ht i hne hne,
    fun i _ _ h26 h27 => hg i h26 h27⟩

theorem rewind_frame (workTape : ℕ) (origin : ℤ) (s : BitRAMState) :
    Frame workTape s (Rewind.finishAt workTape origin s) := by
  simp [Frame, Rewind.finishAt]
  constructor
  · intro i hi
    simp [hi]
  · intro i h24 h25 _ _
    simp [h24, h25]

theorem simulation (workTape : ℕ) (origin : ℤ) (input : List Bool)
    (tape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = BitTape.shifted bits origin) :
    ∃ cost t, cost ≤ 16 * bits.length + 17 ∧
      PricedSteps ((program workTape).next input tape) cost s t ∧
      t.pc = 19 ∧ t.tapes workTape = BitTape.shifted (addressValue bits).bits origin ∧
      (addressValue bits).bits.length ≤ bits.length ∧ Frame workTape s t := by
  obtain ⟨hf, hwordF, hframeF⟩ := ScanForward.shifted_steps workTape origin input tape bits s hpc hword
  have hf' := (contains_forward workTape).call input tape hf
    (by simp [ScanForward.program, ScanForward.finish])
  simp only [BitRAMState.relocate, zero_add] at hf'
  let trimStart := {ScanForward.finish workTape bits.length s with pc := 0}
  have hstart : {ScanForward.finish workTape bits.length s with pc := 5} =
      trimStart.relocate 5 := rfl
  rw [hstart] at hf'
  obtain ⟨trimCost, trimmed, htrimCost, ht, htrimPc, hwordT, hlen, hframeT⟩ :=
    TapeOps.trim_shifted_canonical_steps workTape origin input tape bits trimStart rfl hwordF
  have ht' := (contains_trim workTape).call input tape ht
    (by simp [TapeOps.trim, htrimPc])
  let rewindStart := {trimmed with pc := 0}
  have hr := Rewind.stepsAt workTape origin input tape (addressValue bits).bits.length
    rewindStart rfl
    (by simp [rewindStart, hwordT, BitTape.shiftedEnd])
    (by simp [rewindStart, hwordT, BitTape.shiftedEnd, BitTape.shifted])
    (by
      intro k hk
      refine ⟨(addressValue bits).bits[k], ?_⟩
      simp [rewindStart, hwordT, BitTape.shiftedEnd, BitTape.shifted, hk])
  have hr' := (contains_rewind workTape).call input tape hr
    (by simp [Rewind.program, Rewind.finishAt])
  have hlink : {trimmed with pc := 14} = rewindStart.relocate 14 := rfl
  rw [hlink] at ht'
  let finalState := {Rewind.finishAt workTape origin rewindStart with pc := 19}
  refine ⟨(5 * bits.length + 3 + 1) + (trimCost + 1) +
    (4 * (addressValue bits).bits.length + 5 + 1), finalState, by omega,
    (hf'.trans ht').trans hr', rfl, ?_, hlen, ?_⟩
  · simp [finalState, Rewind.finishAt, rewindStart, hwordT,
      BitTape.shiftedEnd, BitTape.shifted]
  · exact ((frame_of_tapeOps hframeF).trans (frame_of_tapeOps hframeT)).trans
      (rewind_frame workTape origin rewindStart)

theorem run (workTape : ℕ) (origin : ℤ) (input : List Bool)
    (tape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = BitTape.shifted bits origin) :
    ∃ t, (runPriced ((program workTape).next input tape)
        (16 * bits.length + 18) s).finished = some t ∧
      (runPriced ((program workTape).next input tape)
        (16 * bits.length + 18) s).instructions ≤ 16 * bits.length + 17 ∧
      t.tapes workTape = BitTape.shifted (addressValue bits).bits origin ∧
      (addressValue bits).bits.length ≤ bits.length ∧ Frame workTape s t := by
  obtain ⟨cost, t, hc, hs, hp, ht, hlen, hf⟩ := simulation workTape origin input tape bits s hpc hword
  have halt : (program workTape).next input tape t = none := by
    simp [BitRAM.next, program, hp, ScanForward.program, TapeOps.trim, Rewind.program,
      BitRAMInstruction.relocate]
  have hr := hs.runPriced_ge halt (16 * bits.length + 18) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ht, hlen, hf⟩

end Maxwell.Cost.NormalizeWord
