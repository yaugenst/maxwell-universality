import Maxwell.Cost.MemoryWord

namespace Maxwell.Cost.MemoryWord

/-- Consecutive exact bit-memory updates, interpreted by the fixed writer. -/
def writeBits (memory : ℕ → Bool) (address : ℕ) : List Bool → ℕ → Bool
  | [] => memory
  | b :: rest => writeBits (Function.update memory address b) (address + 1) rest

theorem writeBits_outside (memory : ℕ → Bool) (address : ℕ) (word : List Bool)
    (i : ℕ) (hi : i < address ∨ address + word.length ≤ i) :
    writeBits memory address word i = memory i := by
  induction word generalizing memory address with
  | nil => rfl
  | cons b word ih =>
    simp only [writeBits]
    rw [ih _ _ (by simp only [List.length_cons] at hi; omega)]
    exact Function.update_of_ne (by simp only [List.length_cons] at hi; omega) _ _

theorem writeBits_inside (memory : ℕ → Bool) (address : ℕ) (word : List Bool)
    (i : ℕ) (hi : i < word.length) :
    writeBits memory address word (address + i) = word[i] := by
  induction word generalizing memory address i with
  | nil => simp at hi
  | cons b word ih =>
    cases i with
    | zero =>
      simp only [writeBits, Nat.add_zero, List.getElem_cons_zero]
      rw [writeBits_outside _ _ _ _ (Or.inl (by omega))]
      simp
    | succ i =>
      simpa [writeBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (Function.update memory address b) (address + 1) i (by simpa using hi))

/-- Tape 6 is the source word. Its current bit stays in register 28 while
the address loader uses registers 26/27 and performs the charged write. -/
def writeProgram : BitRAM := ⟨
  [.readTape 6 28 27, .branch 27 2 26] ++
  (MemoryBit.program 5 (.writeMemory 28)).code.map (BitRAMInstruction.relocate 2 11) ++
  [.tapeRight 6, .tapeRight 5] ++
  (Increment.program 5).code.map (BitRAMInstruction.relocate 13 25) ++ [.jump 0, .halt]⟩

theorem writeProgram_length : writeProgram.code.length = 27 := by decide

theorem contains_write : writeProgram.Contains (MemoryBit.program 5 (.writeMemory 28)) 2 11 := by decide

theorem write_contains_increment : writeProgram.Contains (Increment.program 5) 13 25 := by decide

def WriteFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (t.tapes 6).cells = (s.tapes 6).cells ∧
  (∀ i, i ≠ 5 → i ≠ 6 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem WriteFrame.refl (s : BitRAMState) : WriteFrame s s := by simp [WriteFrame]

theorem WriteFrame.trans {s t u : BitRAMState}
    (h : WriteFrame s t) (k : WriteFrame t u) : WriteFrame s u := by
  rcases h with ⟨hi, hr, ho, hc, ht, hg⟩
  rcases k with ⟨ki, kr, ko, kc, kt, kg⟩
  exact ⟨ki.trans hi, kr.trans hr, ko.trans ho, kc.trans hc,
    fun i h5 h6 => (kt i h5 h6).trans (ht i h5 h6),
    fun i h26 h27 h28 h29 => (kg i h26 h27 h28 h29).trans (hg i h26 h27 h28 h29)⟩

theorem WriteFrame.of_increment {s t : BitRAMState} (h : Increment.Frame 5 s t) : WriteFrame s t := by
  rcases h with ⟨_, hi, _, hr, ho, ht, hg⟩
  exact ⟨hi, hr, ho, congrArg BitTape.cells (ht 6 (by omega)), fun i h5 _ => ht i h5, hg⟩

def writeFetched (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with pc := 2, registers := Function.update (Function.update s.registers 28 b) 27 true}

def writeStopped (s : BitRAMState) : BitRAMState :=
  {s with pc := 26, registers := Function.update (Function.update s.registers 28 false) 27 false}

def writeAdvanced (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 13
    tapes := Function.update (Function.update s.tapes 6
      {s.tapes 6 with head := (s.tapes 6).head + 1}) 5
      {s.tapes 5 with head := (s.tapes 5).head + 1}}

theorem write_fetch_block (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0) (hread : (s.tapes 6).read = some b) :
    PricedSteps (writeProgram.next input tape) 3 s (writeFetched s b) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, writeProgram, hpc, hread, writeFetched, BitRAMState.setRegister]

theorem write_stop_block (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hread : (s.tapes 6).read = none) :
    PricedSteps (writeProgram.next input tape) 3 s (writeStopped s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, writeProgram, hpc, hread, writeStopped, BitRAMState.setRegister]

theorem write_advance_block (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 11) :
    PricedSteps (writeProgram.next input tape) 2 s (writeAdvanced s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, writeProgram, hpc, writeAdvanced,
    MemoryBit.program, Address.load, Increment.program, BitRAMInstruction.relocate, BitRAMState.setTape]

theorem writeFetched_frame (s : BitRAMState) (b : Bool) : WriteFrame s (writeFetched s b) := by
  simp [WriteFrame, writeFetched]
  intros; simp_all

theorem writeStopped_frame (s : BitRAMState) : WriteFrame s (writeStopped s) := by
  simp [WriteFrame, writeStopped]
  intros; simp_all

theorem writeAdvanced_frame (s : BitRAMState) : WriteFrame s (writeAdvanced s) := by
  simp [WriteFrame, writeAdvanced]
  intros; simp_all

/-- One actual indexed memory write and binary address increment. -/
theorem write_cycle (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (address : List Bool) (origin : ℤ) (b : Bool) (hpc : s.pc = 0)
    (haddress : s.tapes 5 = BitTape.shiftedEnd address origin)
    (hsource : (s.tapes 6).read = some b) :
    ∃ cost t, cost ≤ 15 * address.length + 22 ∧
      PricedSteps (writeProgram.next input tape) cost s t ∧ t.pc = 0 ∧
      t.tapes 5 = BitTape.shiftedEnd (Increment.bits address) origin ∧
      t.tapes 6 = {s.tapes 6 with head := (s.tapes 6).head + 1} ∧
      t.memory = Function.update s.memory (addressValue address) b ∧ WriteFrame s t := by
  have hf := write_fetch_block input tape s b hpc hsource
  obtain ⟨r, hr, hrpc, _, hrmem, hr5, hri, hrr, hro, hrt, hrg⟩ :=
    MemoryBit.write_steps 5 input tape address origin {writeFetched s b with pc := 0} rfl haddress
  let writeState : BitRAMState := {r with pc := 11}
  have hR : PricedSteps (writeProgram.next input tape) (7 * address.length + 7 + 1)
      (writeFetched s b) writeState :=
    contains_write.call_at input tape (writeFetched s b) r rfl hr
      (by simp [MemoryBit.program, Address.load, hrpc, BitRAMInstruction.relocate])
  have hRf : WriteFrame (writeFetched s b) writeState :=
    ⟨hri, hrr, hro, congrArg BitTape.cells (hrt 6 (by omega)),
      fun i h5 _ => hrt i h5, fun i h26 h27 _ _ => hrg i h26 h27⟩
  have hr6 : writeState.tapes 6 = s.tapes 6 := hrt 6 (by omega)
  have hrm : writeState.memory = Function.update s.memory (addressValue address) b := by
    simpa [writeState, writeFetched] using hrmem
  have ha := write_advance_block input tape writeState rfl
  have ha5 : (writeAdvanced writeState).tapes 5 = BitTape.shifted address origin := by
    simp [writeAdvanced, writeState, hr5, BitTape.shifted]
  have ha6 : (writeAdvanced writeState).tapes 6 = {s.tapes 6 with head := (s.tapes 6).head + 1} := by
    simp [writeAdvanced, hr6]
  obtain ⟨incrementCost, u, hcost, hu, hupc, hu5, huf⟩ := Increment.simulation 5 input tape address origin
    {writeAdvanced writeState with pc := 0} rfl ha5
  let final : BitRAMState := {u with pc := 25}
  have hU : PricedSteps (writeProgram.next input tape) (incrementCost + 1)
      (writeAdvanced writeState) final :=
    write_contains_increment.call_at input tape (writeAdvanced writeState) u rfl hu
      (by simp [Increment.program, hupc])
  have hUf : WriteFrame (writeAdvanced writeState) final := WriteFrame.of_increment huf
  have hfooter : PricedSteps (writeProgram.next input tape) 1 final {final with pc := 0} := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, writeProgram, final, MemoryBit.program, Address.load,
      Increment.program, BitRAMInstruction.relocate]
  have hu6 : final.tapes 6 = {s.tapes 6 with head := (s.tapes 6).head + 1} :=
    (huf.2.2.2.2.2.1 6 (by omega)).trans ha6
  have hum : final.memory = Function.update s.memory (addressValue address) b :=
    huf.2.2.1.trans hrm
  exact ⟨_, {final with pc := 0}, by omega, ((hf.trans hR).trans ha).trans (hU.trans hfooter),
    rfl, hu5, hu6, hum,
    ((writeFetched_frame s b).trans hRf).trans ((writeAdvanced_frame writeState).trans hUf)⟩

/-- The writer traverses the finite source exactly once and preserves its
cells. Every random-access write includes its full binary-address charge. -/
theorem write_loop (input : List Bool) (tape : ℕ → Bool) (word address : List Bool)
    (origin : ℤ) (B : ℕ) (s : BitRAMState) (hwidth : address.length ≤ B)
    (hpc : s.pc = 0) (haddress : s.tapes 5 = BitTape.shiftedEnd address origin)
    (hsource : TapeRepresents (s.tapes 6) word) :
    ∃ cost t finalAddress,
      cost ≤ word.length * (15 * (B + word.length) + 22) + 3 ∧
      PricedSteps (writeProgram.next input tape) cost s t ∧ t.pc = 26 ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress origin ∧
      addressValue finalAddress = addressValue address + word.length ∧
      finalAddress.length ≤ B + word.length ∧
      t.tapes 6 = {s.tapes 6 with head := (s.tapes 6).head + word.length} ∧
      t.memory = writeBits s.memory (addressValue address) word ∧ WriteFrame s t := by
  induction word generalizing address B s with
  | nil =>
    refine ⟨3, writeStopped s, address, by simp, write_stop_block input tape s hpc hsource.read,
      rfl, haddress, by simp, by simpa using hwidth, ?_, rfl, writeStopped_frame s⟩
    simp [writeStopped]
  | cons b word ih =>
    obtain ⟨cycleCost, cycled, hc, hs, hp, ha, hsrc, hm, hf⟩ :=
      write_cycle input tape s address origin b hpc haddress hsource.read
    have hcwidth : (Increment.bits address).length ≤ B + 1 :=
      (Increment.bits_length_le address).trans (by omega)
    have hcsource : TapeRepresents (cycled.tapes 6) word := by
      rw [hsrc]
      exact hsource.moveRight
    obtain ⟨cost, t, finalAddress, hcost, hsteps, hpcout, haddressout, hval, hlen,
      hsourceout, hmemoryout, hframe⟩ :=
      ih (Increment.bits address) (B + 1) cycled hcwidth hp ha hcsource
    refine ⟨cycleCost + cost, t, finalAddress, ?_, hs.trans hsteps, hpcout,
      haddressout, ?_, ?_, ?_, ?_, hf.trans hframe⟩
    · simp only [List.length_cons]
      nlinarith
    · simpa [Increment.bits_value, Nat.add_assoc, Nat.add_comm] using hval
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
    · simpa [hsrc, Nat.cast_add, add_assoc, add_comm] using hsourceout
    · simpa [writeBits, hm, Increment.bits_value] using hmemoryout

/-- Exact indexed word write by one fixed finite program. The functional
memory equality determines both the written interval and all other bits. -/
theorem write_simulation (input : List Bool) (tape : ℕ → Bool)
    (address word : List Bool) (addressOrigin sourceOrigin : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (haddress : s.tapes 5 = BitTape.shiftedEnd address addressOrigin)
    (hsource : s.tapes 6 = BitTape.shifted word sourceOrigin) :
    ∃ cost t finalAddress,
      cost ≤ word.length * (15 * (address.length + word.length) + 22) + 3 ∧
      PricedSteps (writeProgram.next input tape) cost s t ∧ t.pc = 26 ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress addressOrigin ∧
      addressValue finalAddress = addressValue address + word.length ∧
      finalAddress.length ≤ address.length + word.length ∧
      t.tapes 6 = BitTape.shiftedEnd word sourceOrigin ∧
      t.memory = writeBits s.memory (addressValue address) word ∧ WriteFrame s t := by
  obtain ⟨cost, t, finalAddress, hc, hs, hp, ha, hv, hl, hsrc, hm, hf⟩ :=
    write_loop input tape word address addressOrigin address.length s le_rfl hpc haddress
      (hsource ▸ BitTape.shifted_represents word sourceOrigin)
  exact ⟨cost, t, finalAddress, hc, hs, hp, ha, hv, hl,
    by simpa [hsource, BitTape.shiftedEnd, BitTape.shifted] using hsrc, hm, hf⟩

theorem write_run (input : List Bool) (tape : ℕ → Bool)
    (address word : List Bool) (addressOrigin sourceOrigin : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (haddress : s.tapes 5 = BitTape.shiftedEnd address addressOrigin)
    (hsource : s.tapes 6 = BitTape.shifted word sourceOrigin) :
    ∃ t finalAddress,
      (runPriced (writeProgram.next input tape)
        (word.length * (15 * (address.length + word.length) + 22) + 4) s).finished = some t ∧
      (runPriced (writeProgram.next input tape)
        (word.length * (15 * (address.length + word.length) + 22) + 4) s).instructions ≤
          word.length * (15 * (address.length + word.length) + 22) + 3 ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress addressOrigin ∧
      addressValue finalAddress = addressValue address + word.length ∧
      finalAddress.length ≤ address.length + word.length ∧
      t.tapes 6 = BitTape.shiftedEnd word sourceOrigin ∧
      t.memory = writeBits s.memory (addressValue address) word ∧ WriteFrame s t := by
  obtain ⟨cost, t, finalAddress, hc, hs, hp, ha, hv, hl, hsrc, hm, hf⟩ :=
    write_simulation input tape address word addressOrigin sourceOrigin s hpc haddress hsource
  have hh : writeProgram.next input tape t = none := by
    simp [BitRAM.next, writeProgram, hp, MemoryBit.program, Address.load,
      Increment.program, BitRAMInstruction.relocate]
  have hrun := hs.runPriced_ge hh
    (word.length * (15 * (address.length + word.length) + 22) + 4) (by omega)
  exact ⟨t, finalAddress, hrun.1, by simpa [hrun.2] using hc, ha, hv, hl, hsrc, hm, hf⟩

end Maxwell.Cost.MemoryWord
