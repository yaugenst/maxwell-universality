import Maxwell.Cost.ParseEntry
import Maxwell.Cost.Structured.Correctness

/-! Natural-number parsing from the actual retained normalization tape.
The executable parser reads and advances tape 85. Its simulation charges
the additional operation of each work-tape read; immutable input is untouched. -/

namespace Maxwell.Cost.NormalizedRecordParser.Natural

def program : BitRAM := ⟨[
  .readTape 85 20 28, .branch 20 2 7, .literal 21 true,
  .writeTape 10 21, .tapeRight 10, .tapeRight 85, .jump 0,
  .tapeRight 85, .tapeLeft 10,
  .readTape 10 20 22, .branch 22 11 18,
  .readTape 85 20 28, .writeTape 11 20, .tapeRight 11, .tapeRight 85,
  .eraseTape 10, .tapeLeft 10, .jump 9, .halt]⟩

private structure Related (stream : List Bool) (inputHead : ℤ)
    (virtual actual : BitRAMState) : Prop where
  pc : actual.pc = virtual.pc
  registers : ∀ i, i ≠ 28 → actual.registers i = virtual.registers i
  tapes : ∀ i, i ≠ 85 → actual.tapes i = virtual.tapes i
  sourceHead : (actual.tapes 85).head = virtual.inputHead
  sourceCells : (actual.tapes 85).cells = (BitTape.ofList stream).cells
  input : actual.inputHead = inputHead
  address : actual.address = virtual.address
  memory : actual.memory = virtual.memory
  random : actual.randomCursor = virtual.randomCursor
  output : actual.output = virtual.output

private theorem Related.read {stream : List Bool} {inputHead : ℤ}
    {s t : BitRAMState} (h : Related stream inputHead s t) :
    (t.tapes 85).read.getD false = inputBit stream s.inputHead := by
  rw [BitTape.read, h.sourceCells, h.sourceHead]
  simp [BitTape.ofList, inputBit]
  split <;> simp_all

private theorem next_simulates (stream input : List Bool) (randomTape : ℕ → Bool)
    (inputHead : ℤ) {s u t : BitRAMState} {extra : ℕ}
    (h : ParseNat.program.next stream randomTape s = some ⟨u, extra⟩)
    (hr : Related stream inputHead s t) :
    ∃ v actualExtra, program.next input randomTape t = some ⟨v, actualExtra⟩ ∧
      Related stream inputHead u v ∧ actualExtra + 1 ≤ 2 * (extra + 1) := by
  have hlt : s.pc < 19 := by
    by_contra! hge
    have hnone : ParseNat.program.code[s.pc]? = none :=
      List.getElem?_eq_none (by simpa [ParseNat.program] using hge)
    simp [BitRAM.next, hnone] at h
  have hread := hr.read
  have hregs := hr.registers
  have htapes := hr.tapes
  generalize hp : s.pc = pc at hlt
  interval_cases pc <;> simp [BitRAM.next, ParseNat.program, hp] at h
  all_goals rcases h with ⟨rfl, rfl⟩
  all_goals simp only [BitRAM.next, program, hr.pc, hp]
  all_goals refine ⟨_, _, rfl, ?_, by omega⟩
  all_goals constructor
  all_goals simp [BitRAMState.setRegister, BitRAMState.setTape,
    Function.update_apply, hr.pc, hr.sourceHead, hr.sourceCells, hr.input,
    hr.address, hr.memory, hr.random, hr.output, hread, hregs, htapes]
  all_goals intros; simp_all

private theorem steps_simulate (stream input : List Bool) (randomTape : ℕ → Bool)
    (inputHead : ℤ) {cost : ℕ} {s u : BitRAMState}
    (h : PricedSteps (ParseNat.program.next stream randomTape) cost s u)
    (t : BitRAMState) (hr : Related stream inputHead s t) :
    ∃ actualCost v, PricedSteps (program.next input randomTape) actualCost t v ∧
      Related stream inputHead u v ∧ actualCost ≤ 2 * cost := by
  induction h generalizing t with
  | refl s => exact ⟨0, t, .refl t, hr, by omega⟩
  | step h rest ih =>
    obtain ⟨v, extra, hv, hrel, hcost⟩ := next_simulates stream input randomTape inputHead h hr
    obtain ⟨restCost, final, hfinal, hrelFinal, hbound⟩ := ih v hrel
    exact ⟨extra + 1 + restCost, final, .step hv hfinal, hrelFinal, by omega⟩

/-- The archive is preserved byte for byte; only its actual head advances. -/
def Frame (target : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (t.tapes 85).cells = (s.tapes 85).cells ∧
  (∀ i, i ≠ 10 → i ≠ target → i ≠ 85 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 20 → i ≠ 21 → i ≠ 22 → i ≠ 28 → t.registers i = s.registers i)

theorem steps (input : List Bool) (randomTape : ℕ → Bool)
    (n : ℕ) (preceding suffix : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hsource : s.tapes 85 =
      {BitTape.ofList (preceding ++ (Codec.nat n ++ suffix)) with head := preceding.length})
    (h10 : s.tapes 10 = BitTape.blank) (h11 : s.tapes 11 = BitTape.blank) :
    ∃ cost t, PricedSteps (program.next input randomTape) cost s t ∧
      cost ≤ 34 * n.bits.length + 14 ∧ t.pc = 18 ∧
      (t.tapes 85).head = preceding.length + (Codec.nat n).length ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧ t.tapes 11 = BitTape.atEnd n.bits ∧ Frame 11 s t := by
  let stream := preceding ++ (Codec.nat n ++ suffix)
  let virtual := {s with inputHead := (preceding.length : ℤ)}
  obtain ⟨u, hu, hp, hh, hc, ho, hf⟩ := ParseNat.parse_nat_steps n preceding suffix randomTape
    virtual hpc rfl h10 h11
  have hrel : Related stream s.inputHead virtual s := by
    constructor <;> simp [virtual, hsource, stream]
  obtain ⟨cost, t, ht, hr, hcost⟩ := steps_simulate stream input randomTape s.inputHead hu s hrel
  refine ⟨cost, t, ht, by omega, hr.pc.trans hp, hr.sourceHead.trans hh,
    (hr.tapes 10 (by decide)).trans hc, (hr.tapes 11 (by decide)).trans ho,
    hr.address.trans hf.1, hr.input, hr.memory.trans hf.2.1,
    hr.random.trans hf.2.2.1, hr.output.trans hf.2.2.2.1, ?_, ?_, ?_⟩
  · simpa [hsource, stream] using hr.sourceCells
  · intro i hi10 hi11 hi85
    exact (hr.tapes i hi85).trans (hf.2.2.2.2.1 i hi10 hi11)
  · intro i hi20 hi21 hi22 hi28
    exact (hr.registers i hi28).trans (hf.2.2.2.2.2 i hi20 hi21 hi22)

def programOn (target : ℕ) : BitRAM := program.renameTapes (Equiv.swap 11 target)

theorem steps_on (target : ℕ) (h10t : target ≠ 10) (h85t : target ≠ 85)
    (input : List Bool) (randomTape : ℕ → Bool)
    (n : ℕ) (preceding suffix : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hsource : s.tapes 85 =
      {BitTape.ofList (preceding ++ (Codec.nat n ++ suffix)) with head := preceding.length})
    (h10 : s.tapes 10 = BitTape.blank) (hout : s.tapes target = BitTape.blank) :
    ∃ cost t, PricedSteps ((programOn target).next input randomTape) cost s t ∧
      cost ≤ 34 * n.bits.length + 14 ∧ t.pc = 18 ∧
      (t.tapes 85).head = preceding.length + (Codec.nat n).length ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧ t.tapes target = BitTape.atEnd n.bits ∧ Frame target s t := by
  let p : Equiv.Perm ℕ := Equiv.swap 11 target
  have hp10 : p 10 = 10 := by simp [p, Equiv.swap_apply_def, h10t.symm]
  have hp85 : p 85 = 85 := by simp [p, Equiv.swap_apply_def, h85t.symm]
  obtain ⟨cost, t, ht, hb, hpc', hh, hc, ho, hf⟩ := steps input randomTape n preceding suffix
    (s.renameTapes p.symm) hpc
    (by simpa [BitRAMState.renameTapes, hp85] using hsource)
    (by simpa [BitRAMState.renameTapes, hp10] using h10)
    (by simpa [BitRAMState.renameTapes, p] using hout)
  have hrenamed := ht.renameTapes p
  rw [BitRAMState.renameTapes_inverse] at hrenamed
  refine ⟨cost, t.renameTapes p, hrenamed, hb, hpc', ?_, ?_, ?_, ?_⟩
  · simpa [BitRAMState.renameTapes, p, Equiv.swap_apply_def, h85t.symm] using hh
  · simpa [BitRAMState.renameTapes, p, Equiv.swap_apply_def, h10t.symm] using hc
  · simpa [BitRAMState.renameTapes, p] using ho
  · refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_, ?_, hf.2.2.2.2.2.2.2⟩
    · simpa [BitRAMState.renameTapes, p, Equiv.swap_apply_def, h85t.symm] using hf.2.2.2.2.2.1
    · intro i hi10 hit hi85
      have hpi10 : p.symm i ≠ 10 := by
        intro heq
        have := congrArg p heq
        simp only [Equiv.apply_symm_apply, hp10] at this
        exact hi10 this
      have hpi85 : p.symm i ≠ 85 := by
        intro heq
        have := congrArg p heq
        simp only [Equiv.apply_symm_apply, hp85] at this
        exact hi85 this
      have hpi11 : p.symm i ≠ 11 := by
        intro heq
        have := congrArg p heq
        simp [p] at this
        exact hit this
      simpa [BitRAMState.renameTapes, Function.comp_def] using
        hf.2.2.2.2.2.2.1 (p.symm i) hpi10 hpi11 hpi85

end Maxwell.Cost.NormalizedRecordParser.Natural
