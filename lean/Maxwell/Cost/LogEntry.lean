import Maxwell.Cost.ParseEntry
import Maxwell.Cost.LogNat

/-! A fixed source-entry parser with retained canonical records. Each call
consumes one sparse entry, appends all its fields to tape 18, and clears
every parser scratch tape by actual instructions before returning. -/

namespace Maxwell.Cost.LogEntry

def program : BitRAM := ⟨
  ParseEntry.program.code.map (BitRAMInstruction.relocate 0 84) ++
  (LogNat.program 15 18).code.map (BitRAMInstruction.relocate 84 120) ++
  (LogNat.program 16 18).code.map (BitRAMInstruction.relocate 120 156) ++
  [.writeTape 18 23, .tapeRight 18] ++
  (LogNat.program 12 18).code.map (BitRAMInstruction.relocate 158 194) ++
  (LogNat.program 13 18).code.map (BitRAMInstruction.relocate 194 230) ++
  [.tapeRight 10, .halt]⟩

theorem parse_contains : program.Contains ParseEntry.program 0 84 := by decide
theorem row_contains : program.Contains (LogNat.program 15 18) 84 120 := by decide
theorem column_contains : program.Contains (LogNat.program 16 18) 120 156 := by decide
theorem numerator_contains : program.Contains (LogNat.program 12 18) 158 194 := by decide
theorem denominator_contains : program.Contains (LogNat.program 13 18) 194 230 := by decide
theorem halt_instruction : program.code[231]? = some .halt := by decide

def Ready (s : BitRAMState) : Prop :=
  s.tapes 10 = BitTape.blank ∧ s.tapes 15 = BitTape.blank ∧
  s.tapes 16 = BitTape.blank ∧ s.tapes 12 = BitTape.blank ∧ s.tapes 13 = BitTape.blank

def width (row column : ℕ) (value : ℚ) : ℕ :=
  row.bits.length + column.bits.length + value.num.natAbs.bits.length + value.den.bits.length

def rowStart (s : BitRAMState) : BitRAMState := {s with pc := 0}

def columnStart (row : ℕ) (preceding : List Bool) (s : BitRAMState) : BitRAMState :=
  {LogNat.finish 15 18 row.bits preceding (rowStart s) with pc := 0}

def signStart (row column : ℕ) (preceding : List Bool) (s : BitRAMState) : BitRAMState :=
  {LogNat.finish 16 18 column.bits (preceding ++ Codec.nat row)
    (columnStart row preceding s) with pc := 156}

def signState (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update s.tapes 18
      {(s.tapes 18).write (some (s.registers 23)) with head := (s.tapes 18).head + 1}}

def numeratorStart (row column : ℕ) (preceding : List Bool)
    (s : BitRAMState) : BitRAMState := signState (signStart row column preceding s)

def signedArchive (row column : ℕ) (value : ℚ) (preceding : List Bool) : List Bool :=
  preceding ++ Codec.nat row ++ Codec.nat column ++ [decide (value.num < 0)]

def denominatorStart (row column : ℕ) (value : ℚ) (preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  {LogNat.finish 12 18 value.num.natAbs.bits (signedArchive row column value preceding)
    (numeratorStart row column preceding s) with pc := 0}

def parsedFinish (row column : ℕ) (value : ℚ) (preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  LogNat.finish 13 18 value.den.bits
    (signedArchive row column value preceding ++ Codec.nat value.num.natAbs)
    (denominatorStart row column value preceding s)

def finish (row column : ℕ) (value : ℚ) (preceding : List Bool)
    (s : BitRAMState) : BitRAMState :=
  {parsedFinish row column value preceding s with
    pc := 231
    tapes := Function.update (parsedFinish row column value preceding s).tapes 10 BitTape.blank}

theorem sign_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) :
    PricedSteps (program.next input tape) 2 {s with pc := 156} ((signState s).relocate 158) := by
  apply executeInstructions_sound (instructions := 2)
  have h156 : program.code[156]? = some (.writeTape 18 23) := by decide
  have h157 : program.code[157]? = some (.tapeRight 18) := by decide
  simp [executeInstructions, BitRAM.next, h156, h157, BitRAMState.setTape,
    BitRAMState.relocate, BitTape.write, signState]

theorem reset_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input tape) 1 {s with pc := 230}
      {s with pc := 231, tapes := Function.update s.tapes 10 BitTape.blank} := by
  apply executeInstructions_sound (instructions := 1)
  have h230 : program.code[230]? = some (.tapeRight 10) := by decide
  simp [executeInstructions, BitRAM.next, h230, BitRAMState.setTape,
    hcount, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

theorem logging_steps (input : List Bool) (tape : ℕ → Bool)
    (row column : ℕ) (value : ℚ) (preceding : List Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd [])
    (hrow : s.tapes 15 = BitTape.atEnd row.bits)
    (hcolumn : s.tapes 16 = BitTape.atEnd column.bits)
    (hnum : s.tapes 12 = BitTape.atEnd value.num.natAbs.bits)
    (hden : s.tapes 13 = BitTape.atEnd value.den.bits)
    (hsign : s.registers 23 = decide (value.num < 0))
    (hlog : s.tapes 18 = BitTape.atEnd preceding) :
    PricedSteps (program.next input tape) (28 * width row column value + 127)
      {s with pc := 84} (finish row column value preceding s) := by
  have hr := row_contains.call input tape
    (LogNat.steps 15 18 (by decide) input tape row.bits preceding (rowStart s) rfl hrow hlog)
    (by simp [LogNat.program, LogNat.finish, Rewind.program, TapeLog.program, TapeReset.program])
  have hrframe := LogNat.finish_frame 15 18 row.bits preceding (rowStart s)
  have hcword : (columnStart row preceding s).tapes 16 = BitTape.atEnd column.bits :=
    (hrframe.2.2.2.2.2.1 16 (by decide) (by decide)).trans hcolumn
  have hclog : (columnStart row preceding s).tapes 18 =
      BitTape.atEnd (preceding ++ Codec.nat row) :=
    LogNat.finish_target 15 18 (by decide) row.bits preceding (rowStart s)
  have hc := column_contains.call input tape
    (LogNat.steps 16 18 (by decide) input tape column.bits (preceding ++ Codec.nat row)
      (columnStart row preceding s) rfl hcword hclog)
    (by simp [LogNat.program, LogNat.finish, Rewind.program, TapeLog.program, TapeReset.program])
  have hcframe := LogNat.finish_frame 16 18 column.bits (preceding ++ Codec.nat row)
    (columnStart row preceding s)
  have hnword : (numeratorStart row column preceding s).tapes 12 =
      BitTape.atEnd value.num.natAbs.bits := by
    have hh := (hcframe.2.2.2.2.2.1 12 (by decide) (by decide)).trans
      ((hrframe.2.2.2.2.2.1 12 (by decide) (by decide)).trans hnum)
    simpa [numeratorStart, signState, signStart] using hh
  have hnlog : (numeratorStart row column preceding s).tapes 18 =
      BitTape.atEnd (signedArchive row column value preceding) := by
    have hs : (signStart row column preceding s).registers 23 = decide (value.num < 0) :=
      (hcframe.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hrframe.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsign)
    have ht : (signStart row column preceding s).tapes 18 =
        BitTape.atEnd (preceding ++ Codec.nat row ++ Codec.nat column) :=
      LogNat.finish_target 16 18 (by decide) column.bits (preceding ++ Codec.nat row)
        (columnStart row preceding s)
    simpa [numeratorStart, signState, ht, hs, signedArchive] using
      BitTape.append_write (preceding ++ Codec.nat row ++ Codec.nat column) (decide (value.num < 0))
  have hn := numerator_contains.call input tape
    (LogNat.steps 12 18 (by decide) input tape value.num.natAbs.bits
      (signedArchive row column value preceding) (numeratorStart row column preceding s)
      rfl hnword hnlog)
    (by simp [LogNat.program, LogNat.finish, Rewind.program, TapeLog.program, TapeReset.program])
  have hnframe := LogNat.finish_frame 12 18 value.num.natAbs.bits
    (signedArchive row column value preceding) (numeratorStart row column preceding s)
  have hdword : (denominatorStart row column value preceding s).tapes 13 =
      BitTape.atEnd value.den.bits := by
    have hh := (hcframe.2.2.2.2.2.1 13 (by decide) (by decide)).trans
      ((hrframe.2.2.2.2.2.1 13 (by decide) (by decide)).trans hden)
    have hh' : (numeratorStart row column preceding s).tapes 13 = BitTape.atEnd value.den.bits := by
      simpa [numeratorStart, signState, signStart] using hh
    exact (hnframe.2.2.2.2.2.1 13 (by decide) (by decide)).trans hh'
  have hdlog : (denominatorStart row column value preceding s).tapes 18 =
      BitTape.atEnd (signedArchive row column value preceding ++ Codec.nat value.num.natAbs) :=
    LogNat.finish_target 12 18 (by decide) value.num.natAbs.bits
      (signedArchive row column value preceding) (numeratorStart row column preceding s)
  have hd := denominator_contains.call input tape
    (LogNat.steps 13 18 (by decide) input tape value.den.bits
      (signedArchive row column value preceding ++ Codec.nat value.num.natAbs)
      (denominatorStart row column value preceding s) rfl hdword hdlog)
    (by simp [LogNat.program, LogNat.finish, Rewind.program, TapeLog.program, TapeReset.program])
  have hdframe := LogNat.finish_frame 13 18 value.den.bits
    (signedArchive row column value preceding ++ Codec.nat value.num.natAbs)
    (denominatorStart row column value preceding s)
  have hcounter : (parsedFinish row column value preceding s).tapes 10 = BitTape.beforeEnd [] := by
    have hh := (hcframe.2.2.2.2.2.1 10 (by decide) (by decide)).trans
      ((hrframe.2.2.2.2.2.1 10 (by decide) (by decide)).trans hcount)
    have hh' : (numeratorStart row column preceding s).tapes 10 = BitTape.beforeEnd [] := by
      simpa [numeratorStart, signState, signStart] using hh
    exact (hdframe.2.2.2.2.2.1 10 (by decide) (by decide)).trans
      ((hnframe.2.2.2.2.2.1 10 (by decide) (by decide)).trans hh')
  convert ((((hr.trans hc).trans (sign_block input tape (signStart row column preceding s))).trans
    hn).trans hd).trans (reset_block input tape (parsedFinish row column value preceding s) hcounter)
    using 1
  · dsimp [width]; omega
  · rfl
  · rfl

theorem finish_log (row column : ℕ) (value : ℚ) (preceding : List Bool) (s : BitRAMState) :
    (finish row column value preceding s).tapes 18 =
      BitTape.atEnd (preceding ++ ParseEntry.encode row column value) := by
  have hh := LogNat.finish_target 13 18 (by decide) value.den.bits
    (signedArchive row column value preceding ++ Codec.nat value.num.natAbs)
    (denominatorStart row column value preceding s)
  simpa [finish, parsedFinish, LogNat.word_bits, signedArchive, ParseEntry.encode,
    Codec.rat, Codec.int, List.append_assoc] using hh

theorem finish_ready (row column : ℕ) (value : ℚ) (preceding : List Bool) (s : BitRAMState) :
    Ready (finish row column value preceding s) := by
  simp [Ready, finish, parsedFinish, denominatorStart, numeratorStart, signState,
    signStart, columnStart, LogNat.finish, TapeReset.finish, LogNat.clearStart,
    TapeLog.finish, LogNat.payloadStart, Rewind.finish, LogNat.rewindStart,
    LogNat.headerEnd, LogNat.headerStart]

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 15 → i ≠ 16 → i ≠ 18 → t.tapes i = s.tapes i) ∧
  (∀ i, i < 20 ∨ 28 < i → t.registers i = s.registers i)

theorem finish_frame (row column : ℕ) (value : ℚ) (preceding : List Bool) (s : BitRAMState) :
    Frame s (finish row column value preceding s) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i h10 h12 h13 h15 h16 h18
    simp [finish, parsedFinish, denominatorStart, numeratorStart, signState,
      signStart, columnStart, rowStart, LogNat.finish, TapeReset.finish, LogNat.clearStart,
      TapeLog.finish, LogNat.payloadStart, Rewind.finish, LogNat.rewindStart,
      LogNat.headerEnd, LogNat.headerStart, h10, h12, h13, h15, h16, h18]
  · intro i hi
    have h24 : i ≠ 24 := by omega
    have h25 : i ≠ 25 := by omega
    have h26 : i ≠ 26 := by omega
    have h27 : i ≠ 27 := by omega
    have h28 : i ≠ 28 := by omega
    simp [finish, parsedFinish, denominatorStart, numeratorStart, signState,
      signStart, columnStart, rowStart, LogNat.finish, TapeReset.finish, LogNat.clearStart,
      TapeLog.finish, LogNat.payloadStart, Rewind.finish, LogNat.rewindStart,
      LogNat.headerEnd, LogNat.headerStart, h24, h25, h26, h27, h28]

theorem steps (row column : ℕ) (value : ℚ) (preceding suffix archive : List Bool)
    (tape : ℕ → Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hready : Ready initial)
    (hlog : initial.tapes 18 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      PricedSteps (program.next (preceding ++ (ParseEntry.encode row column value ++ suffix)) tape)
        (45 * width row column value + 167) initial final ∧
      final.pc = 231 ∧ final.inputHead = initial.inputHead + (ParseEntry.encode row column value).length ∧
      final.tapes 18 = BitTape.atEnd (archive ++ ParseEntry.encode row column value) ∧
      Ready final ∧ Frame initial final := by
  obtain ⟨s, hs, hspc, hshead, hcount, hrow, hcol, hnum, hden, hsign, hframe⟩ :=
    ParseEntry.steps row column value preceding suffix tape initial hpc hhead
      hready.1 hready.2.1 hready.2.2.1 hready.2.2.2.1 hready.2.2.2.2
  let input := preceding ++ (ParseEntry.encode row column value ++ suffix)
  have hp := parse_contains.call input tape hs (by simpa [hspc] using
    (show ParseEntry.program.code[83]? = some .halt by decide))
  simp only [BitRAMState.relocate_zero] at hp
  have hlog' : s.tapes 18 = BitTape.atEnd archive :=
    (hframe.2.2.2.2.1 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hlog
  have hl := logging_steps input tape row column value archive s hcount hrow hcol hnum hden hsign hlog'
  refine ⟨finish row column value archive s, ?_, rfl, hshead,
    finish_log row column value archive s, finish_ready row column value archive s, ?_⟩
  · convert hp.trans hl using 1
    dsimp [width]; omega
  · rcases finish_frame row column value archive s with ⟨ha, hm, hr, ho, ht, hg⟩
    refine ⟨ha.trans hframe.1, hm.trans hframe.2.1, hr.trans hframe.2.2.1,
      ho.trans hframe.2.2.2.1, ?_, ?_⟩
    · intro i h10 h12 h13 h15 h16 h18
      exact (ht i h10 h12 h13 h15 h16 h18).trans
        (hframe.2.2.2.2.1 i h10 h12 h13 h15 h16)
    · intro i hi
      exact (hg i hi).trans (hframe.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega))

end Maxwell.Cost.LogEntry
