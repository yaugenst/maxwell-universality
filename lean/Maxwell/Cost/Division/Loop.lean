import Maxwell.Cost.Division.Program
import Maxwell.Cost.Multiplication.Loop

namespace Maxwell.Cost.Division

abbrev PrefixTape := HornerMultiply.PrefixTape

def fetchedState (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 5
    registers := Function.update (Function.update s.registers 12 b) 13 true
    tapes := Function.update (Function.update s.tapes 3
      {s.tapes 3 with head := (s.tapes 3).head - 1}) 0
      (({s.tapes 0 with head := (s.tapes 0).head - 1}).write (some b))}

def stoppedState (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 80
    registers := Function.update (Function.update s.registers 12 false) 13 false
    tapes := Function.update s.tapes 3 {s.tapes 3 with head := (s.tapes 3).head - 1}}

def emittedState (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update s.registers 14 (!s.registers 2)
    tapes := Function.update s.tapes 4
      (({s.tapes 4 with head := (s.tapes 4).head - 1}).write (some (!s.registers 2)))}

set_option maxRecDepth 4096 in
theorem fetch_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0)
    (hread : (s.tapes 3).cells ((s.tapes 3).head - 1) = some b) :
    PricedSteps (program.next input randomTape) 6 s (fetchedState s b) := by
  apply executeInstructions_sound (instructions := 5)
  simp [executeInstructions, program, BitRAM.next, hpc, hread, BitTape.read,
    fetchedState, BitRAMState.setTape, BitRAMState.setRegister, Function.update_comm]

set_option maxRecDepth 4096 in
theorem stop_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hread : (s.tapes 3).cells ((s.tapes 3).head - 1) = none) :
    PricedSteps (program.next input randomTape) 4 s (stoppedState s) := by
  apply executeInstructions_sound (instructions := 3)
  simp [executeInstructions, program, BitRAM.next, hpc, hread, BitTape.read,
    stoppedState, BitRAMState.setTape, BitRAMState.setRegister]

set_option maxRecDepth 4096 in
theorem emit_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 76) :
    PricedSteps (program.next input randomTape) 4 s (emittedState s) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, program, BitRAM.next, hpc, emittedState,
    Subtraction.program, RewindOvershoot.program, RewindOvershoot.preamble,
    BitRAM.link, Rewind.program, TapeOps.clear, TapeOps.copyClear,
    BitRAMInstruction.relocate, BitRAMState.setTape, BitRAMState.setRegister]

theorem prepend_bit (bits : List Bool) (origin : ℤ) (b : Bool) :
    ({BitTape.shifted bits origin with head := origin - 1}).write (some b) =
      BitTape.shifted (b :: bits) (origin - 1) := by
  apply BitTape.ext
  · rfl
  · funext p
    simp only [BitTape.write, BitTape.shifted]
    by_cases heq : p = origin - 1
    · subst p; simp
    · rw [Function.update_of_ne heq]
      by_cases hp : origin ≤ p
      · have hp' : origin - 1 ≤ p := by omega
        have hi : (p - (origin - 1)).toNat = (p - origin).toNat + 1 := by omega
        simp [hp, hp', hi]
      · have hp' : ¬origin - 1 ≤ p := by omega
        simp [hp, hp']

theorem fetchedState_remainder (s : BitRAMState) (b : Bool)
    (bits : List Bool) (origin : ℤ) (ht : s.tapes 0 = BitTape.shifted bits origin) :
    (fetchedState s b).tapes 0 = BitTape.shifted (b :: bits) (origin - 1) := by
  simpa [fetchedState, ht, BitTape.shifted] using prepend_bit bits origin b

theorem emittedState_quotient (s : BitRAMState)
    (bits : List Bool) (origin : ℤ) (ht : s.tapes 4 = BitTape.shifted bits origin) :
    (emittedState s).tapes 4 = BitTape.shifted ((!s.registers 2) :: bits) (origin - 1) := by
  simpa [emittedState, ht, BitTape.shifted] using prepend_bit bits origin (!s.registers 2)

theorem fetchedState_prefix (s : BitRAMState) (bits : List Bool) (origin : ℤ) (b : Bool)
    (h : PrefixTape (s.tapes 3) (bits ++ [b]) origin) :
    PrefixTape ((fetchedState s b).tapes 3) bits origin := by
  constructor
  · simp [fetchedState, h.head]
    omega
  · simpa [fetchedState] using h.left
  · intro k hk
    have hh := h.cells k (by simp; omega)
    simpa [fetchedState, List.getElem_append_left hk] using hh

end Maxwell.Cost.Division
