import Maxwell.Cost.LogEntry

/-! A finite rational parser appends the exact canonical value to the
separate right-hand-side log on tape 20 and restores its scratch words. -/

namespace Maxwell.Cost.LogRat

def program : BitRAM := ⟨
  ParseRat.program.code.map (BitRAMInstruction.relocate 0 43) ++
  [.writeTape 20 23, .tapeRight 20] ++
  (LogNat.program 12 20).code.map (BitRAMInstruction.relocate 45 81) ++
  (LogNat.program 13 20).code.map (BitRAMInstruction.relocate 81 117) ++
  [.tapeRight 10, .halt]⟩

theorem parse_contains : program.Contains ParseRat.program 0 43 := by decide
theorem numerator_contains : program.Contains (LogNat.program 12 20) 45 81 := by decide
theorem denominator_contains : program.Contains (LogNat.program 13 20) 81 117 := by decide
theorem halt_instruction : program.code[118]? = some .halt := by decide

def Ready (s : BitRAMState) : Prop :=
  s.tapes 10 = BitTape.blank ∧ s.tapes 12 = BitTape.blank ∧ s.tapes 13 = BitTape.blank

def width (q : ℚ) : ℕ := q.num.natAbs.bits.length + q.den.bits.length

def numeratorStart (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update s.tapes 20
      {(s.tapes 20).write (some (s.registers 23)) with head := (s.tapes 20).head + 1}}

def denominatorStart (q : ℚ) (archive : List Bool) (s : BitRAMState) : BitRAMState :=
  {LogNat.finish 12 20 q.num.natAbs.bits (archive ++ [decide (q.num < 0)])
    (numeratorStart s) with pc := 0}

def parsedFinish (q : ℚ) (archive : List Bool) (s : BitRAMState) : BitRAMState :=
  LogNat.finish 13 20 q.den.bits (archive ++ [decide (q.num < 0)] ++ Codec.nat q.num.natAbs)
    (denominatorStart q archive s)

def finish (q : ℚ) (archive : List Bool) (s : BitRAMState) : BitRAMState :=
  {parsedFinish q archive s with
    pc := 118
    tapes := Function.update (parsedFinish q archive s).tapes 10 BitTape.blank}

theorem sign_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) :
    PricedSteps (program.next input tape) 2 {s with pc := 43} ((numeratorStart s).relocate 45) := by
  apply executeInstructions_sound (instructions := 2)
  have h43 : program.code[43]? = some (.writeTape 20 23) := by decide
  have h44 : program.code[44]? = some (.tapeRight 20) := by decide
  simp [executeInstructions, BitRAM.next, h43, h44, BitRAMState.setTape,
    BitRAMState.relocate, BitTape.write, numeratorStart]

theorem reset_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input tape) 1 {s with pc := 117}
      {s with pc := 118, tapes := Function.update s.tapes 10 BitTape.blank} := by
  apply executeInstructions_sound (instructions := 1)
  have h117 : program.code[117]? = some (.tapeRight 10) := by decide
  simp [executeInstructions, BitRAM.next, h117, BitRAMState.setTape,
    hcount, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

theorem logging_steps (input : List Bool) (tape : ℕ → Bool) (q : ℚ)
    (archive : List Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd [])
    (hnum : s.tapes 12 = BitTape.atEnd q.num.natAbs.bits)
    (hden : s.tapes 13 = BitTape.atEnd q.den.bits)
    (hsign : s.registers 23 = decide (q.num < 0))
    (hlog : s.tapes 20 = BitTape.atEnd archive) :
    PricedSteps (program.next input tape) (28 * width q + 65)
      {s with pc := 43} (finish q archive s) := by
  have hnword : (numeratorStart s).tapes 12 = BitTape.atEnd q.num.natAbs.bits := by
    simpa [numeratorStart] using hnum
  have hnlog : (numeratorStart s).tapes 20 = BitTape.atEnd (archive ++ [decide (q.num < 0)]) := by
    simpa [numeratorStart, hlog, hsign] using BitTape.append_write archive (decide (q.num < 0))
  have hn := numerator_contains.call input tape
    (LogNat.steps 12 20 (by decide) input tape q.num.natAbs.bits
      (archive ++ [decide (q.num < 0)]) (numeratorStart s) rfl hnword hnlog)
    (by simp [LogNat.program, LogNat.finish, Rewind.program, TapeLog.program, TapeReset.program])
  have hnframe := LogNat.finish_frame 12 20 q.num.natAbs.bits
    (archive ++ [decide (q.num < 0)]) (numeratorStart s)
  have hdword : (denominatorStart q archive s).tapes 13 = BitTape.atEnd q.den.bits := by
    have hh := hnframe.2.2.2.2.2.1 13 (by decide) (by decide)
    simpa [denominatorStart, numeratorStart, hden] using hh
  have hdlog : (denominatorStart q archive s).tapes 20 =
      BitTape.atEnd (archive ++ [decide (q.num < 0)] ++ Codec.nat q.num.natAbs) :=
    LogNat.finish_target 12 20 (by decide) q.num.natAbs.bits
      (archive ++ [decide (q.num < 0)]) (numeratorStart s)
  have hd := denominator_contains.call input tape
    (LogNat.steps 13 20 (by decide) input tape q.den.bits
      (archive ++ [decide (q.num < 0)] ++ Codec.nat q.num.natAbs)
      (denominatorStart q archive s) rfl hdword hdlog)
    (by simp [LogNat.program, LogNat.finish, Rewind.program, TapeLog.program, TapeReset.program])
  have hdframe := LogNat.finish_frame 13 20 q.den.bits
    (archive ++ [decide (q.num < 0)] ++ Codec.nat q.num.natAbs) (denominatorStart q archive s)
  have hcounter : (parsedFinish q archive s).tapes 10 = BitTape.beforeEnd [] := by
    have hh : (numeratorStart s).tapes 10 = BitTape.beforeEnd [] := by
      simpa [numeratorStart] using hcount
    exact (hdframe.2.2.2.2.2.1 10 (by decide) (by decide)).trans
      ((hnframe.2.2.2.2.2.1 10 (by decide) (by decide)).trans hh)
  convert (((sign_block input tape s).trans hn).trans hd).trans
    (reset_block input tape (parsedFinish q archive s) hcounter) using 1
  · dsimp [width]; omega
  · rfl

theorem finish_log (q : ℚ) (archive : List Bool) (s : BitRAMState) :
    (finish q archive s).tapes 20 = BitTape.atEnd (archive ++ Codec.rat q) := by
  have hh := LogNat.finish_target 13 20 (by decide) q.den.bits
    (archive ++ [decide (q.num < 0)] ++ Codec.nat q.num.natAbs) (denominatorStart q archive s)
  simpa [finish, parsedFinish, LogNat.word_bits, Codec.rat, Codec.int, List.append_assoc] using hh

theorem finish_ready (q : ℚ) (archive : List Bool) (s : BitRAMState) :
    Ready (finish q archive s) := by
  simp [Ready, finish, parsedFinish, denominatorStart, numeratorStart,
    LogNat.finish, TapeReset.finish, LogNat.clearStart, TapeLog.finish,
    LogNat.payloadStart, Rewind.finish, LogNat.rewindStart, LogNat.headerEnd, LogNat.headerStart]

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 20 → t.tapes i = s.tapes i)

theorem finish_frame (q : ℚ) (archive : List Bool) (s : BitRAMState) : Frame s (finish q archive s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i h10 h12 h13 h20
  simp [finish, parsedFinish, denominatorStart, numeratorStart, LogNat.finish, TapeReset.finish,
    LogNat.clearStart, TapeLog.finish, LogNat.payloadStart, Rewind.finish, LogNat.rewindStart,
    LogNat.headerEnd, LogNat.headerStart, h10, h12, h13, h20]

theorem steps (q : ℚ) (preceding suffix archive : List Bool) (tape : ℕ → Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hready : Ready initial)
    (hlog : initial.tapes 20 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      PricedSteps (program.next (preceding ++ (Codec.rat q ++ suffix)) tape)
        (45 * width q + 86) initial final ∧
      final.pc = 118 ∧ final.inputHead = initial.inputHead + (Codec.rat q).length ∧
      final.tapes 20 = BitTape.atEnd (archive ++ Codec.rat q) ∧ Ready final ∧ Frame initial final := by
  obtain ⟨s, hs, hspc, hshead, hcount, hnum, hden, hsign, hframe⟩ :=
    ParseRat.parse_rat_steps q preceding suffix tape initial hpc hhead hready.1 hready.2.1 hready.2.2
  let input := preceding ++ (Codec.rat q ++ suffix)
  have hp := parse_contains.call input tape hs
    (by simpa [hspc] using (show ParseRat.program.code[42]? = some .halt by decide))
  simp only [BitRAMState.relocate_zero] at hp
  have hlog' : s.tapes 20 = BitTape.atEnd archive :=
    (hframe.2.2.2.2.1 20 (by decide) (by decide) (by decide)).trans hlog
  have hl := logging_steps input tape q archive s hcount hnum hden hsign hlog'
  refine ⟨finish q archive s, ?_, rfl, hshead, finish_log q archive s, finish_ready q archive s, ?_⟩
  · convert hp.trans hl using 1
    dsimp [width]; omega
  · rcases finish_frame q archive s with ⟨ha, hm, hr, ho, ht⟩
    refine ⟨ha.trans hframe.1, hm.trans hframe.2.1, hr.trans hframe.2.2.1,
      ho.trans hframe.2.2.2.1, ?_⟩
    intro i h10 h12 h13 h20
    exact (ht i h10 h12 h13 h20).trans (hframe.2.2.2.2.1 i h10 h12 h13)

end Maxwell.Cost.LogRat
