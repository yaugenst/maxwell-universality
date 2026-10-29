import Maxwell.Cost.TapeLog

/-! A finite program appends a self-delimiting binary word to a retained
tape and restores the parsed-word tape to its blank initial state. -/

namespace Maxwell.Cost.LogNat

def program (source target : ℕ) : BitRAM := ⟨
  (Rewind.program source).code.map (BitRAMInstruction.relocate 0 5) ++
  [.literal 28 true] ++
  (TapeLog.program source target true).code.map (BitRAMInstruction.relocate 6 13) ++
  [.literal 26 false, .writeTape target 26, .tapeRight target] ++
  (Rewind.program source).code.map (BitRAMInstruction.relocate 16 21) ++
  (TapeLog.program source target false).code.map (BitRAMInstruction.relocate 21 28) ++
  (TapeReset.program source).code.map (BitRAMInstruction.relocate 28 35) ++ [.halt]⟩

theorem first_contains (source target : ℕ) :
    (program source target).Contains (Rewind.program source) 0 5 := by
  intro i; fin_cases i <;> rfl

theorem header_contains (source target : ℕ) :
    (program source target).Contains (TapeLog.program source target true) 6 13 := by
  intro i; fin_cases i <;> rfl

theorem rewind_contains (source target : ℕ) :
    (program source target).Contains (Rewind.program source) 16 21 := by
  intro i; fin_cases i <;> rfl

theorem payload_contains (source target : ℕ) :
    (program source target).Contains (TapeLog.program source target false) 21 28 := by
  intro i; fin_cases i <;> rfl

theorem clear_contains (source target : ℕ) :
    (program source target).Contains (TapeReset.program source) 28 35 := by
  intro i; fin_cases i <;> rfl

def word (bits : List Bool) : List Bool :=
  List.replicate bits.length true ++ false :: bits

def headerStart (source : ℕ) (s : BitRAMState) : BitRAMState :=
  {Rewind.finish source s with
    pc := 0
    registers := Function.update (Rewind.finish source s).registers 28 true}

def headerEnd (source target : ℕ) (bits preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  {TapeLog.finish source target true bits preceding (headerStart source s) with pc := 13}

def rewindStart (source target : ℕ) (bits preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  let t := headerEnd source target bits preceding s
  {t with
    pc := 0
    registers := Function.update t.registers 26 false
    tapes := Function.update t.tapes target
      {(t.tapes target).write (some false) with head := (t.tapes target).head + 1}}

def payloadStart (source target : ℕ) (bits preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  {Rewind.finish source (rewindStart source target bits preceding s) with pc := 0}

def clearStart (source target : ℕ) (bits preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  {TapeLog.finish source target false bits
    (preceding ++ List.replicate bits.length true ++ [false])
    (payloadStart source target bits preceding s) with pc := 0}

def finish (source target : ℕ) (bits preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  {TapeReset.finish source (clearStart source target bits preceding s) with pc := 35}

theorem literal_block (source target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) :
    PricedSteps ((program source target).next input tape) 1
      {Rewind.finish source s with pc := 5} ((headerStart source s).relocate 6) := by
  apply executeInstructions_sound (instructions := 1)
  simp [executeInstructions, BitRAM.next, program, Rewind.program,
    BitRAMInstruction.relocate, BitRAMState.relocate, BitRAMState.setRegister, headerStart]

theorem separator_block (source target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits preceding : List Bool) (s : BitRAMState) :
    PricedSteps ((program source target).next input tape) 3
      (headerEnd source target bits preceding s)
      ((rewindStart source target bits preceding s).relocate 16) := by
  apply executeInstructions_sound (instructions := 3)
  simp [executeInstructions, BitRAM.next, program, Rewind.program, TapeLog.program,
    BitRAMInstruction.relocate, BitRAMState.relocate, BitRAMState.setRegister,
    BitRAMState.setTape, BitTape.write, headerEnd, rewindStart]

theorem steps (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits preceding : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes source = BitTape.atEnd bits)
    (hlog : s.tapes target = BitTape.atEnd preceding) :
    PricedSteps ((program source target).next input tape)
      (28 * bits.length + 30) s (finish source target bits preceding s) := by
  have hfirst := (first_contains source target).call input tape
    (Rewind.atEnd_steps source input tape bits s hpc hword)
    (by simp [Rewind.program, Rewind.finish])
  have hzero : s.relocate 0 = s := by simp [BitRAMState.relocate]
  rw [hzero] at hfirst
  have hhs : (headerStart source s).tapes source = BitTape.ofList bits := by
    exact Rewind.finish_tape source bits s hword
  have hht : (headerStart source s).tapes target = BitTape.atEnd preceding := by
    simp [headerStart, Rewind.finish, Ne.symm hne, hlog]
  have hheader := (header_contains source target).call input tape
    (TapeLog.steps source target hne true input tape bits preceding (headerStart source s)
      rfl (by rw [hhs]; exact BitTape.ofList_represents bits) hht
      (by simp [headerStart]))
    (by simp [TapeLog.program, TapeLog.finish])
  have hrs : (rewindStart source target bits preceding s).tapes source = BitTape.atEnd bits := by
    simp [rewindStart, headerEnd, TapeLog.finish, headerStart, Rewind.finish, hne,
      hword, BitTape.atEnd]
  have hrt : (rewindStart source target bits preceding s).tapes target =
      BitTape.atEnd (preceding ++ List.replicate bits.length true ++ [false]) := by
    simp only [rewindStart, headerEnd, TapeLog.finish, Function.update_self]
    simpa [show TapeLog.symbol true = (fun _ => true) from rfl] using
      BitTape.append_write (preceding ++ bits.map (TapeLog.symbol true)) false
  have hrewind := (rewind_contains source target).call input tape
    (Rewind.atEnd_steps source input tape bits (rewindStart source target bits preceding s)
      rfl hrs) (by simp [Rewind.program, Rewind.finish])
  have hps : (payloadStart source target bits preceding s).tapes source = BitTape.ofList bits :=
    Rewind.finish_tape source bits (rewindStart source target bits preceding s) hrs
  have hpt : (payloadStart source target bits preceding s).tapes target =
      BitTape.atEnd (preceding ++ List.replicate bits.length true ++ [false]) := by
    simpa [payloadStart, Rewind.finish, Ne.symm hne] using hrt
  have hpayload := (payload_contains source target).call input tape
    (TapeLog.steps source target hne false input tape bits
      (preceding ++ List.replicate bits.length true ++ [false])
      (payloadStart source target bits preceding s) rfl
      (by rw [hps]; exact BitTape.ofList_represents bits) hpt (by simp))
    (by simp [TapeLog.program, TapeLog.finish])
  have hcs : (clearStart source target bits preceding s).tapes source = BitTape.atEnd bits := by
    simp [clearStart, TapeLog.finish, hne, hps, BitTape.ofList, BitTape.atEnd]
  have hclear := (clear_contains source target).call input tape
    (TapeReset.steps source input tape bits (clearStart source target bits preceding s)
      rfl hcs) (by simp [TapeReset.program, TapeReset.finish])
  convert (((((hfirst.trans (literal_block source target input tape s)).trans hheader).trans
    (separator_block source target input tape bits preceding s)).trans hrewind).trans
    hpayload).trans hclear using 1
  · omega
  · rfl

theorem finish_source (source target : ℕ) (bits preceding : List Bool) (s : BitRAMState) :
    (finish source target bits preceding s).tapes source = BitTape.blank := by
  simp [finish, TapeReset.finish]

theorem finish_target (source target : ℕ) (hne : source ≠ target)
    (bits preceding : List Bool) (s : BitRAMState) :
    (finish source target bits preceding s).tapes target =
      BitTape.atEnd (preceding ++ word bits) := by
  simp [finish, TapeReset.finish, Ne.symm hne, clearStart, TapeLog.finish,
    show TapeLog.symbol false = (fun b => b) from rfl, word, List.append_assoc]

def Frame (source target : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ source → i ≠ target → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 →
    t.registers i = s.registers i)

theorem finish_frame (source target : ℕ) (bits preceding : List Bool) (s : BitRAMState) :
    Frame source target s (finish source target bits preceding s) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i hs ht
    simp [finish, TapeReset.finish, clearStart, TapeLog.finish, payloadStart,
      Rewind.finish, rewindStart, headerEnd, headerStart, hs, ht]
  · intro i h24 h25 h26 h27 h28
    simp [finish, TapeReset.finish, clearStart, TapeLog.finish, payloadStart,
      Rewind.finish, rewindStart, headerEnd, headerStart, h24, h25, h26, h27, h28]

theorem word_bits (n : ℕ) : word n.bits = Codec.nat n := rfl

theorem run (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits preceding : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes source = BitTape.atEnd bits)
    (hlog : s.tapes target = BitTape.atEnd preceding) :
    (runPriced ((program source target).next input tape)
      (28 * bits.length + 31) s).finished = some (finish source target bits preceding s) ∧
    (runPriced ((program source target).next input tape)
      (28 * bits.length + 31) s).instructions = 28 * bits.length + 30 := by
  exact (steps source target hne input tape bits preceding s hpc hword hlog).runPriced
    (by simp [BitRAM.next, program, finish, Rewind.program, TapeLog.program, TapeReset.program])

end Maxwell.Cost.LogNat
