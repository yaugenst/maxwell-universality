import Maxwell.Cost.WordTransfer
import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.SourceReplay.Header
open Structured

/-- Move backwards over the unary length header, separator and binary data
of a natural number, using its retained word as the physical loop counter. -/
def program (workTape : ℕ) : BitRAM := ⟨[
  .readTape workTape 24 25, .branch 25 2 6,
  .inputLeft, .inputLeft, .tapeRight workTape, .jump 0,
  .inputLeft, .halt]⟩

def advance (workTape : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    inputHead := s.inputHead - 2
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head + 1},
    registers := Function.update (Function.update s.registers 24 b) 25 true}

def finish (workTape length : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 7
    inputHead := s.inputHead - (2 * length + 1 : ℕ)
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head + length},
    registers := Function.update (Function.update s.registers 24 false) 25 false}

private theorem advance_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0)
    (hread : (s.tapes workTape).read = some b) :
    PricedSteps ((program workTape).next input randomTape) 7 s (advance workTape s b) := by
  apply executeInstructions_sound (instructions := 6)
  simp [executeInstructions, BitRAM.next, program, advance, hpc, hread,
    BitRAMState.setTape, BitRAMState.setRegister]
  omega

private theorem finish_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hread : (s.tapes workTape).read = none) :
    PricedSteps ((program workTape).next input randomTape) 4 s (finish workTape 0 s) := by
  apply executeInstructions_sound (instructions := 3)
  simp [executeInstructions, BitRAM.next, program, finish, hpc, hread,
    BitRAMState.setRegister]

private theorem finish_advance (workTape length : ℕ) (s : BitRAMState) (b : Bool) :
    finish workTape length (advance workTape s b) = finish workTape (length+1) s := by
  simp [finish, advance, Nat.cast_add, Nat.cast_mul, add_assoc, add_comm (1 : ℤ)]
  constructor
  · funext i
    by_cases hi : i = 24 <;> by_cases hj : i = 25 <;> simp [hi, hj]
  · omega

private theorem steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : (s.tapes workTape).Represents bits) :
    PricedSteps ((program workTape).next input randomTape)
      (7 * bits.length + 4) s (finish workTape bits.length s) := by
  induction bits generalizing s with
  | nil =>
    exact finish_block workTape input randomTape s hpc (by simpa [BitTape.read] using hword 0)
  | cons b bits ih =>
    have hs := advance_block workTape input randomTape s b hpc
      (by simpa [BitTape.read] using hword 0)
    have ht := ih (advance workTape s b) rfl (by
      intro k
      have hk := hword (k+1)
      simpa [advance, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hk)
    rw [finish_advance] at ht
    convert hs.trans ht using 1
    simp [Nat.mul_add]
    omega

def code (workTape : ℕ) : Code :=
  .seq (.call (program workTape)) (.call (Rewind.program workTape))

structure Frame (s t : Store) : Prop where
  address : t.val.address = s.val.address
  memory : t.val.memory = s.val.memory
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : t.val.tapes = s.val.tapes

/-- The actual finite routine restores the retained word and moves the
input head by exactly the canonical natural-number encoding length. -/
theorem executes (workTape n : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (s : Store)
    (hw : s.val.tapes workTape = BitTape.shifted n.bits origin) :
    ∃ t : Store, Executes input randomTape (code workTape) (11*n.bits.length+11) s t ∧
      t.val.inputHead = s.val.inputHead - (Codec.nat n).length ∧ Frame s t := by
  have hp : (s.val.tapes workTape).Represents n.bits := by
    rw [hw]
    intro k
    simp [BitTape.shifted]
  have he := steps workTape input randomTape n.bits s.val s.property hp
  let e : Store := Store.ofState (finish workTape n.bits.length s.val)
  have hc : Executes input randomTape (.call (program workTape))
      (7*n.bits.length+5) s e := Executes.call _ _ _ _ he (by rfl)
  have hew : e.val.tapes workTape = BitTape.shiftedEnd n.bits origin := by
    simp [e, Store.ofState, finish, hw, BitTape.shiftedEnd, BitTape.shifted]
  obtain ⟨hr, hrw⟩ := WordTransfer.rewind_shifted workTape origin input randomTape n.bits
    e.val e.property hew
  let t : Store := Store.ofState (Rewind.finishAt workTape origin e.val)
  have hc2 : Executes input randomTape (.call (Rewind.program workTape))
      (4*n.bits.length+6) e t := Executes.call _ _ _ _ hr (by simp [Rewind.program, Rewind.finishAt])
  refine ⟨t, ?_, ?_, ?_⟩
  · convert hc.seq hc2 using 1 <;> first | rfl | omega
  · change s.val.inputHead - (2*n.bits.length+1 : ℕ) = _
    simp [Codec.nat, List.length_append]
    omega
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    funext i
    by_cases hi : i = workTape
    · subst i
      exact hrw.trans hw.symm
    · simp [t, e, Store.ofState, Rewind.finishAt, finish, hi]

end Maxwell.Cost.SourceReplay.Header
