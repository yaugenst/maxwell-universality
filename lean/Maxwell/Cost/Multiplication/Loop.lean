import Maxwell.Cost.Multiplication.Tapes

namespace Maxwell.Cost.HornerMultiply

/-- State after fetching the next most-significant multiplier bit and
performing the one-cell binary shift of the current accumulator. -/
def shiftedState (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := if b then 9 else 2
    registers := Function.update (Function.update (Function.update s.registers 12 b) 13 true) 14 false
    tapes := Function.update (Function.update s.tapes 3
      {s.tapes 3 with head := (s.tapes 3).head - 1}) 0
      (({s.tapes 0 with head := (s.tapes 0).head - 1}).write (some false))}

def stoppedState (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 71
    registers := Function.update (Function.update s.registers 12 false) 13 false
    tapes := Function.update s.tapes 3 {s.tapes 3 with head := (s.tapes 3).head - 1}}

set_option maxRecDepth 4096 in
theorem shift_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 2)
    (hread : (s.tapes 3).cells ((s.tapes 3).head - 1) = some b) :
    PricedSteps (program.next input randomTape) 8 s (shiftedState s b) := by
  apply executeInstructions_sound (instructions := 7)
  simp [executeInstructions, program, BitRAM.next, hpc, hread, BitTape.read,
    shiftedState, BitRAMState.setTape, BitRAMState.setRegister, Function.update_comm]

theorem stop_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 2)
    (hread : (s.tapes 3).cells ((s.tapes 3).head - 1) = none) :
    PricedSteps (program.next input randomTape) 4 s (stoppedState s) := by
  apply executeInstructions_sound (instructions := 3)
  simp [executeInstructions, program, BitRAM.next, hpc, hread, BitTape.read,
    stoppedState, BitRAMState.setTape, BitRAMState.setRegister]

@[simp] theorem stoppedState_halt (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) : program.next input randomTape (stoppedState s) = none := by
  rfl

theorem shiftedState_accumulator (s : BitRAMState) (b : Bool)
    (bits : List Bool) (origin : ℤ) (ht : s.tapes 0 = BitTape.shifted bits origin) :
    (shiftedState s b).tapes 0 = BitTape.shifted (false :: bits) (origin - 1) := by
  simpa [shiftedState, ht, BitTape.shifted] using BitTape.prepend_false bits origin

/-- Finite fetch for the multiplicand's zero special case. An empty word
is handled without searching an entirely blank tape for an origin. -/
def initialState (s : BitRAMState) : BitRAMState :=
  {s with
    pc := if (s.tapes 1).read.isSome then 2 else 71
    registers := Function.update (Function.update s.registers 12
      ((s.tapes 1).read.getD false)) 13 ((s.tapes 1).read.isSome)}

theorem initial_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) :
    PricedSteps (program.next input randomTape) 3 s (initialState s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, program, BitRAM.next, hpc, initialState,
    BitRAMState.setRegister]

/-- The unprocessed low-order prefix of a multiplier. Cells to its right
may contain already processed bits and are not silently erased. -/
structure PrefixTape (tape : BitTape) (bits : List Bool) (origin : ℤ) : Prop where
  head : tape.head = origin + bits.length
  left : tape.cells (origin - 1) = none
  cells : ∀ k (hk : k < bits.length), tape.cells (origin + k) = some bits[k]

theorem PrefixTape.shiftedEnd (bits : List Bool) (origin : ℤ) :
    PrefixTape (BitTape.shiftedEnd bits origin) bits origin := by
  constructor
  · rfl
  · simp [BitTape.shiftedEnd, BitTape.shifted]
  · intro k hk
    simp [BitTape.shiftedEnd, BitTape.shifted, hk]

theorem PrefixTape.last_read {tape : BitTape} {bits : List Bool} {origin : ℤ} {b : Bool}
    (h : PrefixTape tape (bits ++ [b]) origin) :
    tape.cells (tape.head - 1) = some b := by
  have hp : tape.head - 1 = origin + bits.length := by
    rw [h.head]
    simp
    omega
  rw [hp]
  have hh := h.cells bits.length (by simp)
  simpa using hh

theorem PrefixTape.nil_read {tape : BitTape} {origin : ℤ}
    (h : PrefixTape tape [] origin) : tape.cells (tape.head - 1) = none := by
  simpa [h.head] using h.left

theorem shiftedState_prefix (s : BitRAMState) (bits : List Bool) (origin : ℤ) (b : Bool)
    (h : PrefixTape (s.tapes 3) (bits ++ [b]) origin) :
    PrefixTape ((shiftedState s b).tapes 3) bits origin := by
  constructor
  · simp [shiftedState, h.head]
    omega
  · simpa [shiftedState] using h.left
  · intro k hk
    have hh := h.cells k (by simp; omega)
    simpa [shiftedState, List.getElem_append_left hk] using hh


end Maxwell.Cost.HornerMultiply
