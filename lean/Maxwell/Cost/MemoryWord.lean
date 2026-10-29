import Maxwell.Cost.MemoryBit
import Maxwell.Cost.Increment
import Maxwell.Cost.Arithmetic.Words

namespace Maxwell.Cost.MemoryWord

/-- Consecutive little-endian memory bits, with no host arithmetic in the
machine that realizes this specification. -/
def readBits (memory : ℕ → Bool) (address : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => memory address :: readBits memory (address + 1) n

@[simp] theorem readBits_length (memory : ℕ → Bool) (address width : ℕ) :
    (readBits memory address width).length = width := by
  induction width generalizing address <;> simp_all [readBits]

theorem readBits_getElem (memory : ℕ → Bool) (address width i : ℕ) (hi : i < width) :
    (readBits memory address width)[i]'(by simpa using hi) = memory (address + i) := by
  induction width generalizing address i with
  | zero => omega
  | succ width ih =>
    cases i with
    | zero => simp [readBits]
    | succ i =>
      simpa [readBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (address + 1) i (by omega))

/-- Tape 5 is the binary address at its end, tape 6 supplies one clock cell
per requested bit, and tape 7 receives the memory word. -/
def readProgram : BitRAM := ⟨
  [.readTape 6 26 27, .branch 27 2 28] ++
  (MemoryBit.program 5 (.readMemory 28)).code.map (BitRAMInstruction.relocate 2 11) ++
  [.writeTape 7 28, .tapeRight 7, .tapeRight 6, .tapeRight 5] ++
  (Increment.program 5).code.map (BitRAMInstruction.relocate 15 27) ++ [.jump 0, .halt]⟩

theorem program_length : readProgram.code.length = 29 := by decide

theorem contains_read : readProgram.Contains (MemoryBit.program 5 (.readMemory 28)) 2 11 := by decide

theorem contains_increment : readProgram.Contains (Increment.program 5) 15 27 := by decide

/-- Memory is read-only; clock cells, sign register and all unrelated state
are preserved. The random-access address register is intentionally rebuilt. -/
def Frame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (t.tapes 6).cells = (s.tapes 6).cells ∧
  (∀ i, i ≠ 5 → i ≠ 6 → i ≠ 7 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨hi, hm, hr, ho, hc, ht, hg⟩
  rcases k with ⟨ki, km, kr, ko, kc, kt, kg⟩
  exact ⟨ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho, kc.trans hc,
    fun i h5 h6 h7 => (kt i h5 h6 h7).trans (ht i h5 h6 h7),
    fun i h26 h27 h28 h29 => (kg i h26 h27 h28 h29).trans (hg i h26 h27 h28 h29)⟩

theorem Frame.of_read {s t : BitRAMState} (h : MemoryBit.ReadFrame 5 s t) : Frame s t := by
  rcases h with ⟨hi, hm, hr, ho, ht, hg⟩
  exact ⟨hi, hm, hr, ho, congrArg BitTape.cells (ht 6 (by omega)),
    fun i h5 _ _ => ht i h5, fun i h26 h27 h28 _ => hg i h26 h27 h28⟩

theorem Frame.of_increment {s t : BitRAMState} (h : Increment.Frame 5 s t) : Frame s t := by
  rcases h with ⟨_, hi, hm, hr, ho, ht, hg⟩
  exact ⟨hi, hm, hr, ho, congrArg BitTape.cells (ht 6 (by omega)),
    fun i h5 _ _ => ht i h5, hg⟩

def fetched (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with pc := 2, registers := Function.update (Function.update s.registers 26 b) 27 true}

def stopped (s : BitRAMState) : BitRAMState :=
  {s with pc := 28, registers := Function.update (Function.update s.registers 26 false) 27 false}

def advanced (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 15
    tapes := Function.update (Function.update (Function.update s.tapes 7
      {(s.tapes 7).write (some (s.registers 28)) with head := (s.tapes 7).head + 1}) 6
      {s.tapes 6 with head := (s.tapes 6).head + 1}) 5
      {s.tapes 5 with head := (s.tapes 5).head + 1}}

theorem fetch_block (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0) (hread : (s.tapes 6).read = some b) :
    PricedSteps (readProgram.next input tape) 3 s (fetched s b) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, readProgram, hpc, hread, fetched, BitRAMState.setRegister]

theorem stop_block (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hread : (s.tapes 6).read = none) :
    PricedSteps (readProgram.next input tape) 3 s (stopped s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, readProgram, hpc, hread, stopped, BitRAMState.setRegister]

theorem advance_block (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 11) :
    PricedSteps (readProgram.next input tape) 4 s (advanced s) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, readProgram, hpc, advanced,
    MemoryBit.program, Address.load, Increment.program, BitRAMInstruction.relocate,
    BitRAMState.setTape, BitTape.write]

theorem fetched_frame (s : BitRAMState) (b : Bool) : Frame s (fetched s b) := by
  simp [Frame, fetched]
  intros; simp_all

theorem stopped_frame (s : BitRAMState) : Frame s (stopped s) := by
  simp [Frame, stopped]
  intros; simp_all

theorem advanced_frame (s : BitRAMState) : Frame s (advanced s) := by
  simp [Frame, advanced]
  intros; simp_all

/-- One executed memory read plus the actual binary address increment. -/
theorem cycle (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (address : List Bool) (origin : ℤ) (b : Bool) (hpc : s.pc = 0)
    (haddress : s.tapes 5 = BitTape.shiftedEnd address origin)
    (hclock : (s.tapes 6).read = some b) :
    ∃ cost t, cost ≤ 15 * address.length + 24 ∧
      PricedSteps (readProgram.next input tape) cost s t ∧ t.pc = 0 ∧
      t.tapes 5 = BitTape.shiftedEnd (Increment.bits address) origin ∧
      t.tapes 6 = {s.tapes 6 with head := (s.tapes 6).head + 1} ∧
      TapeWrites (s.tapes 7) (t.tapes 7) [s.memory (addressValue address)] ∧ Frame s t := by
  have hf := fetch_block input tape s b hpc hclock
  obtain ⟨r, hr, hrpc, _, hrbit, hr5, hrf⟩ := MemoryBit.read_steps 5 input tape address origin
    {fetched s b with pc := 0} rfl haddress
  let readState : BitRAMState := {r with pc := 11}
  have hR : PricedSteps (readProgram.next input tape) (7 * address.length + 7 + 1)
      (fetched s b) readState :=
    contains_read.call_at input tape (fetched s b) r rfl hr
      (by simp [MemoryBit.program, Address.load, hrpc, BitRAMInstruction.relocate])
  have hRf : Frame (fetched s b) readState := Frame.of_read hrf
  have hr6 : readState.tapes 6 = s.tapes 6 := hrf.2.2.2.2.1 6 (by omega)
  have hr7 : readState.tapes 7 = s.tapes 7 := hrf.2.2.2.2.1 7 (by omega)
  have ha := advance_block input tape readState rfl
  have ha5 : (advanced readState).tapes 5 = BitTape.shifted address origin := by
    simp [advanced, readState, hr5, BitTape.shifted]
  have ha6 : (advanced readState).tapes 6 = {s.tapes 6 with head := (s.tapes 6).head + 1} := by
    simp [advanced, hr6]
  have ha7 : TapeWrites (s.tapes 7) ((advanced readState).tapes 7)
      [s.memory (addressValue address)] := by
    have hraw7 : r.tapes 7 = s.tapes 7 := hr7
    constructor <;> simp [advanced, readState, hraw7, hrbit, fetched, writeCells, BitTape.write]
  obtain ⟨incrementCost, u, hcost, hu, hupc, hu5, huf⟩ := Increment.simulation 5 input tape address origin
    {advanced readState with pc := 0} rfl ha5
  let final : BitRAMState := {u with pc := 27}
  have hU : PricedSteps (readProgram.next input tape) (incrementCost + 1)
      (advanced readState) final :=
    contains_increment.call_at input tape (advanced readState) u rfl hu
      (by simp [Increment.program, hupc])
  have hUf : Frame (advanced readState) final := Frame.of_increment huf
  have hfooter : PricedSteps (readProgram.next input tape) 1 final {final with pc := 0} := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, readProgram, final, MemoryBit.program, Address.load,
      Increment.program, BitRAMInstruction.relocate]
  have hu6 : final.tapes 6 = {s.tapes 6 with head := (s.tapes 6).head + 1} :=
    (huf.2.2.2.2.2.1 6 (by omega)).trans ha6
  have hu7 : TapeWrites (s.tapes 7) (final.tapes 7) [s.memory (addressValue address)] := by
    change TapeWrites (s.tapes 7) (u.tapes 7) _
    rw [huf.2.2.2.2.2.1 7 (by omega)]
    exact ha7
  exact ⟨_, {final with pc := 0}, by omega, ((hf.trans hR).trans ha).trans (hU.trans hfooter),
    rfl, hu5, hu6, hu7, ((fetched_frame s b).trans hRf).trans ((advanced_frame readState).trans hUf)⟩

/-- The clock word controls the entire read; address width growth is bounded
using the proved incrementer, including arbitrary high zero padding. -/
theorem loop (input : List Bool) (tape : ℕ → Bool) (clock address : List Bool)
    (origin : ℤ) (B : ℕ) (s : BitRAMState) (hwidth : address.length ≤ B)
    (hpc : s.pc = 0) (haddress : s.tapes 5 = BitTape.shiftedEnd address origin)
    (hclock : TapeRepresents (s.tapes 6) clock) :
    ∃ cost t finalAddress,
      cost ≤ clock.length * (15 * (B + clock.length) + 24) + 3 ∧
      PricedSteps (readProgram.next input tape) cost s t ∧ t.pc = 28 ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress origin ∧
      addressValue finalAddress = addressValue address + clock.length ∧
      finalAddress.length ≤ B + clock.length ∧
      t.tapes 6 = {s.tapes 6 with head := (s.tapes 6).head + clock.length} ∧
      TapeWrites (s.tapes 7) (t.tapes 7) (readBits s.memory (addressValue address) clock.length) ∧
      Frame s t := by
  induction clock generalizing address B s with
  | nil =>
    refine ⟨3, stopped s, address, by simp, stop_block input tape s hpc hclock.read,
      rfl, haddress, by simp, by simpa using hwidth, ?_, ?_, stopped_frame s⟩
    · simp [stopped]
    · exact TapeWrites.refl _
  | cons b clock ih =>
    obtain ⟨cycleCost, cycled, hc, hs, hp, ha, hclk, hw, hf⟩ :=
      cycle input tape s address origin b hpc haddress hclock.read
    have hcwidth : (Increment.bits address).length ≤ B + 1 :=
      (Increment.bits_length_le address).trans (by omega)
    have hcclock : TapeRepresents (cycled.tapes 6) clock := by
      rw [hclk]
      exact hclock.moveRight
    obtain ⟨cost, t, finalAddress, hcost, hsteps, hpcout, haddressout, hval, hlen,
      hclockout, hwordout, hframe⟩ :=
      ih (Increment.bits address) (B + 1) cycled hcwidth hp ha hcclock
    refine ⟨cycleCost + cost, t, finalAddress, ?_, hs.trans hsteps, hpcout,
      haddressout, ?_, ?_, ?_, ?_, hf.trans hframe⟩
    · simp only [List.length_cons]
      nlinarith
    · simpa [Increment.bits_value, Nat.add_assoc, Nat.add_comm] using hval
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
    · simpa [hclk, Nat.cast_add, add_assoc, add_comm] using hclockout
    · have hrest : TapeWrites (cycled.tapes 7) (t.tapes 7)
          (readBits s.memory (addressValue address + 1) clock.length) := by
        simpa [hf.2.1, Increment.bits_value] using hwordout
      simpa [readBits] using hw.trans hrest

/-- A real fixed program reads a word of arbitrary width from indexed bit
memory, charging every address push, full-address read, and increment. -/
theorem simulation (input : List Bool) (tape : ℕ → Bool)
    (address clock : List Bool) (addressOrigin clockOrigin outputOrigin : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (haddress : s.tapes 5 = BitTape.shiftedEnd address addressOrigin)
    (hclock : s.tapes 6 = BitTape.shifted clock clockOrigin)
    (houtput : s.tapes 7 = {BitTape.blank with head := outputOrigin}) :
    ∃ cost t finalAddress,
      cost ≤ clock.length * (15 * (address.length + clock.length) + 24) + 3 ∧
      PricedSteps (readProgram.next input tape) cost s t ∧ t.pc = 28 ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress addressOrigin ∧
      addressValue finalAddress = addressValue address + clock.length ∧
      finalAddress.length ≤ address.length + clock.length ∧
      t.tapes 6 = BitTape.shiftedEnd clock clockOrigin ∧
      t.tapes 7 = BitTape.shiftedEnd (readBits s.memory (addressValue address) clock.length) outputOrigin ∧
      Frame s t := by
  obtain ⟨cost, t, finalAddress, hc, hs, hp, ha, hv, hl, hclk, hw, hf⟩ :=
    loop input tape clock address addressOrigin address.length s le_rfl hpc haddress
      (hclock ▸ BitTape.shifted_represents clock clockOrigin)
  exact ⟨cost, t, finalAddress, hc, hs, hp, ha, hv, hl,
    by simpa [hclock, BitTape.shiftedEnd, BitTape.shifted] using hclk, hw.blank houtput, hf⟩

theorem run (input : List Bool) (tape : ℕ → Bool)
    (address clock : List Bool) (addressOrigin clockOrigin outputOrigin : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (haddress : s.tapes 5 = BitTape.shiftedEnd address addressOrigin)
    (hclock : s.tapes 6 = BitTape.shifted clock clockOrigin)
    (houtput : s.tapes 7 = {BitTape.blank with head := outputOrigin}) :
    ∃ t finalAddress,
      (runPriced (readProgram.next input tape)
        (clock.length * (15 * (address.length + clock.length) + 24) + 4) s).finished = some t ∧
      (runPriced (readProgram.next input tape)
        (clock.length * (15 * (address.length + clock.length) + 24) + 4) s).instructions ≤
          clock.length * (15 * (address.length + clock.length) + 24) + 3 ∧
      t.tapes 5 = BitTape.shiftedEnd finalAddress addressOrigin ∧
      addressValue finalAddress = addressValue address + clock.length ∧
      finalAddress.length ≤ address.length + clock.length ∧
      t.tapes 6 = BitTape.shiftedEnd clock clockOrigin ∧
      t.tapes 7 = BitTape.shiftedEnd (readBits s.memory (addressValue address) clock.length) outputOrigin ∧
      Frame s t := by
  obtain ⟨cost, t, finalAddress, hc, hs, hp, ha, hv, hl, hclk, hw, hf⟩ :=
    simulation input tape address clock addressOrigin clockOrigin outputOrigin s hpc haddress hclock houtput
  have hh : readProgram.next input tape t = none := by
    simp [BitRAM.next, readProgram, hp, MemoryBit.program, Address.load,
      Increment.program, BitRAMInstruction.relocate]
  have hrun := hs.runPriced_ge hh
    (clock.length * (15 * (address.length + clock.length) + 24) + 4) (by omega)
  exact ⟨t, finalAddress, hrun.1, by simpa [hrun.2] using hc, ha, hv, hl, hclk, hw, hf⟩

end Maxwell.Cost.MemoryWord
