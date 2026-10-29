import Maxwell.Cost.Structured.Correctness
import Maxwell.Cost.WordTransfer

namespace Maxwell.Cost.DecoderParser.ArchiveRewind
open Structured

/-- Rewind the sequential input once for every bit in the actual archive.
The blank symbol, rather than a host-supplied length, terminates this pass. -/
def program : BitRAM := ⟨[
  .tapeLeft 18, .readTape 18 24 25, .branch 25 3 5,
  .inputLeft, .jump 0, .tapeRight 18, .halt]⟩

def retreat (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    inputHead := s.inputHead - 1
    tapes := Function.update s.tapes 18 {s.tapes 18 with head := (s.tapes 18).head - 1},
    registers := Function.update (Function.update s.registers 24 b) 25 true}

def finish (length : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 6
    inputHead := s.inputHead - length
    tapes := Function.update s.tapes 18 {s.tapes 18 with head := 0},
    registers := Function.update (Function.update s.registers 24 false) 25 false}

private theorem retreat_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0)
    (hread : (s.tapes 18).cells ((s.tapes 18).head - 1) = some b) :
    PricedSteps (program.next input randomTape) 6 s (retreat s b) := by
  apply executeInstructions_sound (instructions := 5)
  simp [executeInstructions, BitRAM.next, program, hpc,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, hread, retreat]

private theorem finish_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hhead : (s.tapes 18).head = 0)
    (hread : (s.tapes 18).cells (-1) = none) :
    PricedSteps (program.next input randomTape) 5 s (finish 0 s) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, program, hpc,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, hread, hhead, finish]

private theorem finish_retreat (length : ℕ) (s : BitRAMState) (b : Bool) :
    finish length (retreat s b) = finish (length + 1) s := by
  simp [finish, retreat]
  constructor
  · funext i
    by_cases hi : i = 24 <;> by_cases hj : i = 25 <;> simp [hi, hj]
  · omega

theorem steps (input : List Bool) (randomTape : ℕ → Bool)
    (length : ℕ) (s : BitRAMState) (hpc : s.pc = 0)
    (hhead : (s.tapes 18).head = length)
    (hblank : (s.tapes 18).cells (-1) = none)
    (hpresent : ∀ k < length, ∃ b, (s.tapes 18).cells k = some b) :
    PricedSteps (program.next input randomTape)
      (6 * length + 5) s (finish length s) := by
  induction length generalizing s with
  | zero => exact finish_block input randomTape s hpc hhead hblank
  | succ length ih =>
    obtain ⟨b, hb⟩ := hpresent length (by omega)
    have hread : (s.tapes 18).cells ((s.tapes 18).head - 1) = some b := by
      simpa [hhead] using hb
    have hs := retreat_block input randomTape s b hpc hread
    have ht := ih (retreat s b) rfl
      (by simp [retreat, hhead])
      (by simpa [retreat] using hblank)
      (by intro k hk; simpa [retreat] using hpresent k (by omega))
    rw [finish_retreat] at ht
    convert hs.trans ht using 1
    omega

/-- Actual charged archive rewind, with every other tape and memory intact. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (s : Store) (harchive : s.val.tapes 18 = BitTape.shiftedEnd word 0) :
    Executes input randomTape (.call program) (6 * word.length + 6) s
      (Store.ofState (finish word.length s.val)) ∧
    (finish word.length s.val).inputHead = s.val.inputHead - word.length ∧
    (finish word.length s.val).tapes 18 = BitTape.ofList word ∧
    (finish word.length s.val).memory = s.val.memory ∧
    (finish word.length s.val).randomCursor = s.val.randomCursor ∧
    (finish word.length s.val).output = s.val.output ∧
    (∀ j, j ≠ 18 → (finish word.length s.val).tapes j = s.val.tapes j) := by
  have he := steps input randomTape word.length s.val s.property
    (by simp [harchive, BitTape.shiftedEnd])
    (by simp [harchive, BitTape.shiftedEnd, BitTape.shifted])
    (by intro k hk; exact ⟨word[k], by simp [harchive, BitTape.shiftedEnd, BitTape.shifted, hk]⟩)
  refine ⟨?_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · convert Executes.call program s _ _ he (by rfl) using 1
  · simp [finish, harchive, BitTape.shiftedEnd, BitTape.shifted, BitTape.ofList]
  · intro j hj
    simp [finish, hj]

end Maxwell.Cost.DecoderParser.ArchiveRewind
