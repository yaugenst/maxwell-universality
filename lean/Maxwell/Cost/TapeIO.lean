import Maxwell.Cost.Scan
import Maxwell.Cost.Blocks

/-! Finite bit-output routines. A word is traversed cell by cell until its
blank terminator; every read, head move, branch, and emitted bit is charged.
The header mode emits one `true` per word cell for the self-delimiting codec. -/

namespace Maxwell.Cost.TapeIO

def program (workTape : ℕ) (header : Bool) : BitRAM := ⟨[
  .readTape workTape 26 27, .branch 27 2 5,
  .output (if header then 28 else 26), .tapeRight workTape, .jump 0, .halt]⟩

def symbol (header b : Bool) : Bool := if header then true else b

def advanceState (workTape : ℕ) (header : Bool) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head + 1}
    registers := Function.update (Function.update s.registers 26 b) 27 true
    output := symbol header b :: s.output}

def finish (workTape : ℕ) (header : Bool) (bits : List Bool) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 5
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head + bits.length}
    registers := Function.update (Function.update s.registers 26 false) 27 false
    output := (bits.map (symbol header)).reverse ++ s.output}

theorem advance_block (workTape : ℕ) (header : Bool) (input : List Bool)
    (randomTape : ℕ → Bool) (s : BitRAMState) (b : Bool) (hpc : s.pc = 0)
    (hread : (s.tapes workTape).read = some b)
    (hheader : header = true → s.registers 28 = true) :
    PricedSteps ((program workTape header).next input randomTape) 6 s
      (advanceState workTape header s b) := by
  apply executeInstructions_sound (instructions := 5)
  cases header with
  | false =>
    simp [executeInstructions, BitRAM.next, program, advanceState, hpc, hread,
      BitRAMState.setTape, BitRAMState.setRegister, symbol]
  | true =>
    simp [executeInstructions, BitRAM.next, program, advanceState, hpc, hread,
      BitRAMState.setTape, BitRAMState.setRegister, symbol, hheader rfl]

theorem finish_block (workTape : ℕ) (header : Bool) (input : List Bool)
    (randomTape : ℕ → Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hread : (s.tapes workTape).read = none) :
    PricedSteps ((program workTape header).next input randomTape) 3 s
      (finish workTape header [] s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, finish, hpc, hread,
    BitRAMState.setRegister]

theorem finish_advance (workTape : ℕ) (header : Bool) (bits : List Bool)
    (s : BitRAMState) (b : Bool) :
    finish workTape header bits (advanceState workTape header s b) =
      finish workTape header (b :: bits) s := by
  simp [finish, advanceState, add_assoc, add_comm (1 : ℤ)]
  funext i
  by_cases hi : i = 26 <;> by_cases hj : i = 27 <;> simp [hi, hj]

/-- Actual execution for a word at any tape offset. The represented word
is a proof parameter, not an instruction supplying a precomputed output. -/
theorem steps (workTape : ℕ) (header : Bool) (input : List Bool)
    (randomTape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : (s.tapes workTape).Represents bits)
    (hheader : header = true → s.registers 28 = true) :
    PricedSteps ((program workTape header).next input randomTape)
      (6 * bits.length + 3) s (finish workTape header bits s) := by
  induction bits generalizing s with
  | nil =>
    apply finish_block workTape header input randomTape s hpc
    simpa [BitTape.read] using hword 0
  | cons b bits ih =>
    have hread : (s.tapes workTape).read = some b := by
      simpa [BitTape.read] using hword 0
    have hs := advance_block workTape header input randomTape s b hpc hread hheader
    have ht := ih (advanceState workTape header s b) rfl
      (by
        intro k
        have hk := hword (k + 1)
        simpa [advanceState, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hk)
      (by simpa [advanceState] using hheader)
    rw [finish_advance] at ht
    convert hs.trans ht using 1
    simp [Nat.mul_add]
    omega

theorem run (workTape : ℕ) (header : Bool) (input : List Bool)
    (randomTape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : (s.tapes workTape).Represents bits)
    (hheader : header = true → s.registers 28 = true) :
    (runPriced ((program workTape header).next input randomTape)
      (6 * bits.length + 4) s).finished = some (finish workTape header bits s) ∧
    (runPriced ((program workTape header).next input randomTape)
      (6 * bits.length + 4) s).instructions = 6 * bits.length + 3 := by
  exact (steps workTape header input randomTape bits s hpc hword hheader).runPriced
    (by simp [BitRAM.next, program, finish])

end Maxwell.Cost.TapeIO
