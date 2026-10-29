import Maxwell.Cost.ParseNat

/-! A literal tape-head rewind routine used between parsing and arithmetic.
Its input head is exactly at the end of a contiguous word; no numerical word
length or unbounded pointer arithmetic is supplied as a free instruction. -/

namespace Maxwell.Cost.Rewind

def program (workTape : ℕ) : BitRAM := ⟨[
  .tapeLeft workTape, .readTape workTape 24 25,
  .branch 25 0 3, .tapeRight workTape, .halt]⟩

def retreat (workTape : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head - 1}
    registers := Function.update (Function.update s.registers 24 b) 25 true}

def finish (workTape : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 4
    tapes := Function.update s.tapes workTape {s.tapes workTape with head := 0}
    registers := Function.update (Function.update s.registers 24 false) 25 false}

def finishAt (workTape : ℕ) (origin : ℤ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 4
    tapes := Function.update s.tapes workTape {s.tapes workTape with head := origin}
    registers := Function.update (Function.update s.registers 24 false) 25 false}

theorem retreat_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0)
    (hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = some b) :
    PricedSteps ((program workTape).next input randomTape) 4 s (retreat workTape s b) := by
  apply executeInstructions_sound (instructions := 3)
  simp [executeInstructions, BitRAM.next, program, hpc,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, hread, retreat]

theorem finish_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hhead : (s.tapes workTape).head = 0)
    (hread : (s.tapes workTape).cells (-1) = none) :
    PricedSteps ((program workTape).next input randomTape) 5 s (finish workTape s) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, program, hpc,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, hread, hhead, finish]

theorem finishAt_block (workTape : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hhead : (s.tapes workTape).head = origin)
    (hread : (s.tapes workTape).cells (origin - 1) = none) :
    PricedSteps ((program workTape).next input randomTape) 5 s (finishAt workTape origin s) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, program, hpc,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, hread, hhead, finishAt]

theorem finishAt_retreat (workTape : ℕ) (origin : ℤ) (s : BitRAMState) (b : Bool) :
    finishAt workTape origin (retreat workTape s b) = finishAt workTape origin s := by
  simp [finishAt, retreat]
  funext i
  by_cases hi : i = 24 <;> by_cases hj : i = 25 <;> simp [hi, hj]

/-- The same finite code rewinds words at any integer tape offset. The
origin appears only in this proof contract, never as a machine instruction. -/
theorem stepsAt (workTape : ℕ) (origin : ℤ) (input : List Bool) (randomTape : ℕ → Bool)
    (length : ℕ) (s : BitRAMState) (hpc : s.pc = 0)
    (hhead : (s.tapes workTape).head = origin + length)
    (hblank : (s.tapes workTape).cells (origin - 1) = none)
    (hpresent : ∀ k < length, ∃ b, (s.tapes workTape).cells (origin + k) = some b) :
    PricedSteps ((program workTape).next input randomTape)
      (4 * length + 5) s (finishAt workTape origin s) := by
  induction length generalizing s with
  | zero =>
    exact finishAt_block workTape origin input randomTape s hpc (by simpa using hhead) hblank
  | succ length ih =>
    obtain ⟨b, hb⟩ := hpresent length (by omega)
    have hposition : (s.tapes workTape).head - 1 = origin + length := by
      rw [hhead]
      push_cast
      omega
    have hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = some b := by
      simpa only [hposition] using hb
    have hs := retreat_block workTape input randomTape s b hpc hread
    have htail := ih (retreat workTape s b) rfl
      (by simpa only [retreat, Function.update_self] using hposition)
      (by simpa [retreat] using hblank)
      (by intro k hk; simpa [retreat] using hpresent k (by omega))
    rw [finishAt_retreat] at htail
    convert hs.trans htail using 1
    omega

/-- A generic contiguous finite word is enough; values may include zero
bits, because the interpreter tests the distinct blank symbol. -/
theorem steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (length : ℕ) (s : BitRAMState) (hpc : s.pc = 0)
    (hhead : (s.tapes workTape).head = length)
    (hblank : (s.tapes workTape).cells (-1) = none)
    (hpresent : ∀ k < length, ∃ b, (s.tapes workTape).cells k = some b) :
    PricedSteps ((program workTape).next input randomTape)
      (4 * length + 5) s (finish workTape s) := by
  induction length generalizing s with
  | zero => exact finish_block workTape input randomTape s hpc hhead hblank
  | succ length ih =>
    obtain ⟨b, hb⟩ := hpresent length (by omega)
    have hread : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = some b := by
      simpa [hhead] using hb
    have hs := retreat_block workTape input randomTape s b hpc hread
    have htail := ih (retreat workTape s b) rfl
      (by simp [retreat, hhead])
      (by simpa [retreat] using hblank)
      (by intro k hk; simpa [retreat] using hpresent k (by omega))
    have hfinish : finish workTape (retreat workTape s b) = finish workTape s := by
      simp [finish, retreat]
      funext i
      by_cases hi : i = 24 <;> by_cases hj : i = 25 <;>
        simp [hi, hj]
    rw [hfinish] at htail
    convert hs.trans htail using 1
    omega

/-- Exact parser-to-arithmetic handoff for every finite binary word. -/
theorem atEnd_steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes workTape = BitTape.atEnd bits) :
    PricedSteps ((program workTape).next input randomTape)
      (4 * bits.length + 5) s (finish workTape s) := by
  apply steps workTape input randomTape bits.length s hpc
  · simp [htape, BitTape.atEnd]
  · simp [htape, BitTape.atEnd, BitTape.ofList]
  · intro k hk
    refine ⟨bits[k], ?_⟩
    simp [htape, BitTape.atEnd, BitTape.ofList, hk]

theorem finish_tape (workTape : ℕ) (bits : List Bool) (s : BitRAMState)
    (htape : s.tapes workTape = BitTape.atEnd bits) :
    (finish workTape s).tapes workTape = BitTape.ofList bits := by
  simp [finish, htape, BitTape.atEnd, BitTape.ofList]

theorem run_atEnd (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes workTape = BitTape.atEnd bits) :
    (runPriced ((program workTape).next input randomTape) (4 * bits.length + 6) s).finished =
        some (finish workTape s) ∧
      (runPriced ((program workTape).next input randomTape) (4 * bits.length + 6) s).instructions =
        4 * bits.length + 5 := by
  exact (atEnd_steps workTape input randomTape bits s hpc htape).runPriced
    (by simp [BitRAM.next, finish, program])

end Maxwell.Cost.Rewind
