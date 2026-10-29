import Maxwell.Cost.TapeIO

/-! A fixed program serializes an arbitrary binary word in the canonical
self-delimiting natural-number format. It emits the length header by
traversal, rewinds the physical tape, and emits the original bits. -/

namespace Maxwell.Cost.EmitNat

def program (workTape : ℕ) : BitRAM := ⟨
  [.literal 28 true] ++
  ((TapeIO.program workTape true).code.map (BitRAMInstruction.relocate 1 7)) ++
  [.literal 26 false, .output 26] ++
  ((Rewind.program workTape).code.map (BitRAMInstruction.relocate 9 14)) ++
  ((TapeIO.program workTape false).code.map (BitRAMInstruction.relocate 14 20)) ++
  [.halt]⟩

theorem contains_header (workTape : ℕ) :
    (program workTape).Contains (TapeIO.program workTape true) 1 7 := by
  intro i
  fin_cases i <;> rfl

theorem contains_rewind (workTape : ℕ) :
    (program workTape).Contains (Rewind.program workTape) 9 14 := by
  intro i
  fin_cases i <;> rfl

theorem contains_payload (workTape : ℕ) :
    (program workTape).Contains (TapeIO.program workTape false) 14 20 := by
  intro i
  fin_cases i <;> rfl

def headerStart (s : BitRAMState) : BitRAMState :=
  {s with pc := 0, registers := Function.update s.registers 28 true}

def separatorStart (workTape : ℕ) (bits : List Bool) (s : BitRAMState) : BitRAMState :=
  {TapeIO.finish workTape true bits (headerStart s) with pc := 7}

def rewindStart (workTape : ℕ) (bits : List Bool) (s : BitRAMState) : BitRAMState :=
  let t := separatorStart workTape bits s
  {t with
    pc := 0
    registers := Function.update t.registers 26 false
    output := false :: t.output}

def payloadStart (workTape : ℕ) (bits : List Bool) (s : BitRAMState) : BitRAMState :=
  {Rewind.finishAt workTape (s.tapes workTape).head (rewindStart workTape bits s)
    with pc := 0}

def finish (workTape : ℕ) (bits : List Bool) (s : BitRAMState) : BitRAMState :=
  {TapeIO.finish workTape false bits (payloadStart workTape bits s) with pc := 20}

def word (bits : List Bool) : List Bool :=
  List.replicate bits.length true ++ false :: bits

theorem first_block (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) :
    PricedSteps ((program workTape).next input tape) 1 s ((headerStart s).relocate 1) := by
  apply executeInstructions_sound (instructions := 1)
  simp [executeInstructions, BitRAM.next, program, hpc,
    BitRAMState.setRegister, headerStart, BitRAMState.relocate]

theorem separator_block (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) :
    PricedSteps ((program workTape).next input tape) 2
      (separatorStart workTape bits s) ((rewindStart workTape bits s).relocate 9) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, separatorStart, TapeIO.program,
    Rewind.program, BitRAMInstruction.relocate, rewindStart,
    BitRAMState.setRegister, BitRAMState.relocate]

/-- The routine uses the tape's actual blank sentinel to find the start;
neither the word length nor its value is a machine instruction argument. -/
theorem steps (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : (s.tapes workTape).Represents bits)
    (hblank : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = none) :
    PricedSteps ((program workTape).next input tape)
      (16 * bits.length + 17) s (finish workTape bits s) := by
  have hfirst := first_block workTape input tape s hpc
  have hheader := TapeIO.steps workTape true input tape bits (headerStart s) rfl
    hword (by simp [headerStart])
  have hheader' := (contains_header workTape).call input tape hheader
    (by simp [TapeIO.program, TapeIO.finish])
  have hseparator := separator_block workTape input tape bits s
  have hrewind := Rewind.stepsAt workTape (s.tapes workTape).head input tape bits.length
    (rewindStart workTape bits s) rfl
    (by simp [rewindStart, separatorStart, TapeIO.finish, headerStart])
    (by simpa [rewindStart, separatorStart, TapeIO.finish, headerStart] using hblank)
    (by
      intro k hk
      refine ⟨bits[k], ?_⟩
      simpa [rewindStart, separatorStart, TapeIO.finish, headerStart, hk] using hword k)
  have hrewind' := (contains_rewind workTape).call input tape hrewind
    (by simp [Rewind.program, Rewind.finishAt])
  have hpayload := TapeIO.steps workTape false input tape bits (payloadStart workTape bits s)
    rfl (by simpa [payloadStart, Rewind.finishAt, rewindStart, separatorStart,
      TapeIO.finish, headerStart] using hword) (by simp)
  have hpayload' := (contains_payload workTape).call input tape hpayload
    (by simp [TapeIO.program, TapeIO.finish])
  have hlink : {Rewind.finishAt workTape (s.tapes workTape).head
      (rewindStart workTape bits s) with pc := 14} =
      (payloadStart workTape bits s).relocate 14 := rfl
  rw [hlink] at hrewind'
  convert (((hfirst.trans hheader').trans hseparator).trans hrewind').trans hpayload' using 1
  · omega
  · rfl

theorem finish_output (workTape : ℕ) (bits : List Bool) (s : BitRAMState) :
    (finish workTape bits s).output = (word bits).reverse ++ s.output := by
  simp [finish, payloadStart, Rewind.finishAt, rewindStart, separatorStart,
    TapeIO.finish, headerStart,
    show TapeIO.symbol false = (fun b => b) from rfl,
    show TapeIO.symbol true = (fun _ => true) from rfl,
    word, List.reverse_append,
    List.append_assoc]

theorem finish_tape (workTape : ℕ) (bits : List Bool) (s : BitRAMState) :
    (finish workTape bits s).tapes workTape =
      {s.tapes workTape with head := (s.tapes workTape).head + bits.length} := by
  simp [finish, payloadStart, Rewind.finishAt, rewindStart, separatorStart,
    TapeIO.finish, headerStart]

theorem word_bits (n : ℕ) : word n.bits = Codec.nat n := rfl

theorem run (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : (s.tapes workTape).Represents bits)
    (hblank : (s.tapes workTape).cells ((s.tapes workTape).head - 1) = none) :
    (runPriced ((program workTape).next input tape)
      (16 * bits.length + 18) s).finished = some (finish workTape bits s) ∧
    (runPriced ((program workTape).next input tape)
      (16 * bits.length + 18) s).instructions = 16 * bits.length + 17 := by
  exact (steps workTape input tape bits s hpc hword hblank).runPriced
    (by simp [BitRAM.next, program, TapeIO.program, Rewind.program, finish,
      BitRAMInstruction.relocate])

end Maxwell.Cost.EmitNat
