import Maxwell.Cost.Arithmetic.Words

namespace Maxwell.Cost.Copy

/-- Non-destructive copy: only the source head moves; its cells remain
available for subsequent rational arithmetic calls. -/
def program (source target : ℕ) : BitRAM := ⟨[
  .readTape source 26 27, .branch 27 2 6, .writeTape target 26,
  .tapeRight source, .tapeRight target, .jump 0, .halt]⟩

def nextState (source target : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update (Function.update s.registers 26 b) 27 true
    tapes := Function.update (Function.update s.tapes source
      {s.tapes source with head := (s.tapes source).head + 1}) target
      {(s.tapes target).write (some b) with head := (s.tapes target).head + 1}}

def exitState (s : BitRAMState) : BitRAMState :=
  {s with pc := 6, registers := Function.update (Function.update s.registers 26 false) 27 false}

theorem block (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) (b : Bool)
    (hpc : s.pc = 0) (hread : (s.tapes source).read = some b) :
    PricedSteps ((program source target).next input tape) 7 s (nextState source target s b) := by
  apply executeInstructions_sound (instructions := 6)
  simp [executeInstructions, program, BitRAM.next, hpc, hread, nextState,
    BitRAMState.setRegister, BitRAMState.setTape, hne, Ne.symm hne, Function.update_comm hne, BitTape.write]

theorem exit_block (source target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hread : (s.tapes source).read = none) :
    PricedSteps ((program source target).next input tape) 3 s (exitState s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, program, BitRAM.next, hpc, hread, exitState, BitRAMState.setRegister]

theorem nextState_frame (source target : ℕ) (s : BitRAMState) (b : Bool) :
    TapeOps.Frame source target s (nextState source target s b) := by
  simp [TapeOps.Frame, nextState]
  constructor <;> intros <;> simp_all

theorem exitState_frame (source target : ℕ) (s : BitRAMState) :
    TapeOps.Frame source target s (exitState s) := by
  simp [TapeOps.Frame, exitState]
  intros
  simp_all

theorem simulation (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) (bits : List Bool)
    (hpc : s.pc = 0) (hword : TapeRepresents (s.tapes source) bits) :
    ∃ t, PricedSteps ((program source target).next input tape) (7 * bits.length + 3) s t ∧
      t.pc = 6 ∧ TapeWrites (s.tapes target) (t.tapes target) bits ∧
      t.tapes source = {s.tapes source with head := (s.tapes source).head + bits.length} ∧
      TapeOps.Frame source target s t := by
  induction bits generalizing s with
  | nil =>
    refine ⟨exitState s, ?_, rfl, TapeWrites.refl _, ?_, exitState_frame source target s⟩
    · simpa using exit_block source target input tape s hpc hword.read
    · simp [exitState]
  | cons b bits ih =>
    have hs := block source target hne input tape s b hpc hword.read
    have hnext : TapeRepresents ((nextState source target s b).tapes source) bits := by
      simpa [nextState, hne] using hword.moveRight
    obtain ⟨t, ht, hp, hw, hsource, hf⟩ := ih (nextState source target s b) rfl hnext
    have hw0 : TapeWrites (s.tapes target) ((nextState source target s b).tapes target) [b] := by
      constructor <;> simp [nextState, writeCells, BitTape.write]
    refine ⟨t, ?_, hp, ?_, ?_, (nextState_frame source target s b).trans hf⟩
    · convert hs.trans ht using 1
      simp
      omega
    · simpa using hw0.trans hw
    · simpa [nextState, hne, Nat.cast_add, add_assoc, add_comm] using hsource

/-- Arbitrary integer origins and complete global source/destination
contents. The exact cost includes the final blank read and branch. -/
theorem shifted_steps (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (sourceOrigin targetOrigin : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hs : s.tapes source = BitTape.shifted bits sourceOrigin)
    (ht : s.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, PricedSteps ((program source target).next input tape) (7 * bits.length + 3) s t ∧
      t.pc = 6 ∧ t.tapes source = BitTape.shiftedEnd bits sourceOrigin ∧
      t.tapes target = BitTape.shiftedEnd bits targetOrigin ∧ TapeOps.Frame source target s t := by
  obtain ⟨t, he, hp, hw, hsrc, hf⟩ := simulation source target hne input tape s bits hpc
    (hs ▸ BitTape.shifted_represents bits sourceOrigin)
  exact ⟨t, he, hp, by simpa [hs, BitTape.shiftedEnd, BitTape.shifted] using hsrc, hw.blank ht, hf⟩

end Maxwell.Cost.Copy
