import Maxwell.Cost.TapeReset
import Maxwell.Cost.Blocks
import Maxwell.Cost.Scan

/-! Actual append operations on a retained sequential bit log. Unlike the
external output channel, this tape remains available to subsequent code. -/

namespace Maxwell.Cost.TapeLog

def symbol (header b : Bool) : Bool := if header then true else b

def program (source target : ℕ) (header : Bool) : BitRAM := ⟨[
  .readTape source 26 27, .branch 27 2 6,
  .writeTape target (if header then 28 else 26),
  .tapeRight target, .tapeRight source, .jump 0, .halt]⟩

def advanceState (source target : ℕ) (header : Bool) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update (Function.update s.tapes source
      {s.tapes source with head := (s.tapes source).head + 1}) target
      {(s.tapes target).write (some (symbol header b)) with head := (s.tapes target).head + 1}
    registers := Function.update (Function.update s.registers 26 b) 27 true}

def finish (source target : ℕ) (header : Bool) (bits preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 6
    tapes := Function.update (Function.update s.tapes source
      {s.tapes source with head := (s.tapes source).head + bits.length}) target
      (BitTape.atEnd (preceding ++ bits.map (symbol header)))
    registers := Function.update (Function.update s.registers 26 false) 27 false}

theorem advance_block (source target : ℕ) (hne : source ≠ target) (header : Bool)
    (input : List Bool) (randomTape : ℕ → Bool) (s : BitRAMState) (b : Bool)
    (hpc : s.pc = 0) (hread : (s.tapes source).read = some b)
    (hheader : header = true → s.registers 28 = true) :
    PricedSteps ((program source target header).next input randomTape) 7 s
      (advanceState source target header s b) := by
  apply executeInstructions_sound (instructions := 6)
  cases header with
  | false =>
    simp [executeInstructions, BitRAM.next, program, hpc, hread,
      BitRAMState.setTape, BitRAMState.setRegister, BitTape.write, advanceState, symbol,
      hne, Function.update_comm hne]
  | true =>
    simp [executeInstructions, BitRAM.next, program, hpc, hread,
      BitRAMState.setTape, BitRAMState.setRegister, BitTape.write, advanceState, symbol,
      hne, Function.update_comm hne, hheader rfl]

theorem finish_block (source target : ℕ) (header : Bool)
    (input : List Bool) (randomTape : ℕ → Bool) (preceding : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hread : (s.tapes source).read = none)
    (htarget : s.tapes target = BitTape.atEnd preceding) :
    PricedSteps ((program source target header).next input randomTape) 3 s
      (finish source target header [] preceding s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, hpc, hread,
    BitRAMState.setRegister, finish, ← htarget]

theorem finish_advance (source target : ℕ) (hne : source ≠ target) (header : Bool)
    (bits preceding : List Bool) (s : BitRAMState) (b : Bool) :
    finish source target header bits (preceding ++ [symbol header b])
      (advanceState source target header s b) =
        finish source target header (b :: bits) preceding s := by
  simp [finish, advanceState, Function.update_comm hne,
    List.append_assoc, add_assoc, add_comm (1 : ℤ)]
  funext i
  by_cases hi : i = 26 <;> by_cases hj : i = 27 <;> simp [hi, hj]

theorem steps (source target : ℕ) (hne : source ≠ target) (header : Bool)
    (input : List Bool) (randomTape : ℕ → Bool) (bits preceding : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hword : (s.tapes source).Represents bits)
    (htarget : s.tapes target = BitTape.atEnd preceding)
    (hheader : header = true → s.registers 28 = true) :
    PricedSteps ((program source target header).next input randomTape)
      (7 * bits.length + 3) s (finish source target header bits preceding s) := by
  induction bits generalizing s preceding with
  | nil =>
    apply finish_block source target header input randomTape preceding s hpc _ htarget
    simpa [BitTape.read] using hword 0
  | cons b bits ih =>
    have hread : (s.tapes source).read = some b := by simpa [BitTape.read] using hword 0
    have hs := advance_block source target hne header input randomTape s b hpc hread hheader
    have hnext : (advanceState source target header s b).tapes target =
        BitTape.atEnd (preceding ++ [symbol header b]) := by
      simp only [advanceState, Function.update_self, htarget]
      exact BitTape.append_write _ _
    have ht := ih (preceding := preceding ++ [symbol header b])
      (advanceState source target header s b) rfl
      (by
        intro k
        have hh := hword (k + 1)
        simpa [advanceState, hne, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hh)
      hnext (by simpa [advanceState] using hheader)
    rw [finish_advance source target hne] at ht
    convert hs.trans ht using 1
    simp
    omega

theorem finish_source (source target : ℕ) (hne : source ≠ target) (header : Bool)
    (bits preceding : List Bool) (s : BitRAMState) :
    (finish source target header bits preceding s).tapes source =
      {s.tapes source with head := (s.tapes source).head + bits.length} := by
  simp [finish, hne]

theorem finish_target (source target : ℕ) (header : Bool) (bits preceding : List Bool)
    (s : BitRAMState) :
    (finish source target header bits preceding s).tapes target =
      BitTape.atEnd (preceding ++ bits.map (symbol header)) := by simp [finish]

theorem finish_frame (source target : ℕ) (header : Bool) (bits preceding : List Bool)
    (s : BitRAMState) :
    TapeOps.Frame source target s (finish source target header bits preceding s) := by
  simp [TapeOps.Frame, finish, Function.update_apply]
  constructor
  · intro i hi hj; simp [hi, hj]
  · intro i hi hj; simp [hi, hj]

end Maxwell.Cost.TapeLog
