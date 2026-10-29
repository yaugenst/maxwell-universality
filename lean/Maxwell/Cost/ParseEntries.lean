import Maxwell.Cost.LogEntries

/-! The sparse-entry list count is read from the input, stored as a physical
binary word, and used by a finite counted parser. All records remain in the
retained tape log. The list length is never an instruction parameter. -/

namespace Maxwell.Cost.ParseEntries

def program : BitRAM := ⟨
  (ParseNat.programOn 14).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10] ++
  (Rewind.program 14).code.map (BitRAMInstruction.relocate 20 25) ++
  LogEntries.program.code.map (BitRAMInstruction.relocate 25 275) ++ [.halt]⟩

theorem header_contains : program.Contains (ParseNat.programOn 14) 0 19 := by decide
theorem rewind_contains : program.Contains (Rewind.program 14) 20 25 := by decide
set_option maxRecDepth 4096 in
theorem loop_contains : program.Contains LogEntries.program 25 275 := by decide
theorem halt_instruction : program.code[275]? = some .halt := by decide

def price (entries : List LogEntries.Entry) : ℕ :=
  21 * entries.length.bits.length + 16 + LogEntries.price entries.length.bits entries

def resetState (s : BitRAMState) : BitRAMState :=
  {s with pc := 0, tapes := Function.update s.tapes 10 BitTape.blank}

def loopStart (s : BitRAMState) : BitRAMState :=
  {Rewind.finish 14 (resetState s) with pc := 0}

theorem reset_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input tape) 1 {s with pc := 19} ((resetState s).relocate 20) := by
  apply executeInstructions_sound (instructions := 1)
  have h19 : program.code[19]? = some (.tapeRight 10) := by decide
  simp [executeInstructions, BitRAM.next, h19, BitRAMState.setTape, BitRAMState.relocate,
    resetState, hcount, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

theorem steps (entries : List LogEntries.Entry) (preceding suffix archive : List Bool)
    (tape : ℕ → Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hready : LogEntry.Ready initial)
    (hcounter : initial.tapes 14 = BitTape.blank)
    (hlog : initial.tapes 18 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      PricedSteps (program.next
        (preceding ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)) tape)
        (price entries) initial final ∧
      final.pc = 275 ∧
      final.inputHead = initial.inputHead + (Codec.list LogEntries.encodeEntry entries).length ∧
      final.tapes 18 = BitTape.atEnd (archive ++ LogEntries.records entries) ∧
      LogEntry.Ready final ∧ LogEntries.Frame initial final := by
  let input := preceding ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)
  obtain ⟨s, hs, hspc, hshead, hscount, hsout, hframe⟩ :=
    ParseNat.parse_on_steps 14 (by decide) entries.length preceding
      (LogEntries.records entries ++ suffix) tape initial hpc hhead hready.1 hcounter
  have hi : preceding ++ (Codec.nat entries.length ++ (LogEntries.records entries ++ suffix)) = input := by
    simp [input, Codec.list, LogEntries.records, List.append_assoc]
  rw [hi] at hs
  have hp := header_contains.call input tape hs (by
    simp [ParseNat.programOn, BitRAM.renameTapes, ParseNat.program, hspc,
      BitRAMInstruction.renameTapes])
  simp only [BitRAMState.relocate_zero] at hp
  have hrword : (resetState s).tapes 14 = BitTape.atEnd entries.length.bits := by
    simpa [resetState] using hsout
  have hr := rewind_contains.call input tape
    (Rewind.atEnd_steps 14 input tape entries.length.bits (resetState s) rfl hrword)
    (by simp [Rewind.program, Rewind.finish])
  have hlword : (loopStart s).tapes 14 = BitTape.ofList entries.length.bits :=
    Rewind.finish_tape 14 entries.length.bits (resetState s) hrword
  have hlhead : (loopStart s).inputHead = (preceding ++ Codec.nat entries.length).length := by
    simpa [loopStart, Rewind.finish, resetState, hhead] using hshead
  have hlother (i : ℕ) (hi10 : i ≠ 10) (hi14 : i ≠ 14) :
      (loopStart s).tapes i = initial.tapes i := by
    simpa [loopStart, Rewind.finish, resetState, hi10, hi14] using
      hframe.2.2.2.2.1 i hi10 hi14
  have hlready : LogEntry.Ready (loopStart s) := by
    refine ⟨?_, (hlother 15 (by decide) (by decide)).trans hready.2.1,
      (hlother 16 (by decide) (by decide)).trans hready.2.2.1,
      (hlother 12 (by decide) (by decide)).trans hready.2.2.2.1,
      (hlother 13 (by decide) (by decide)).trans hready.2.2.2.2⟩
    simp [loopStart, Rewind.finish, resetState]
  have hllog : (loopStart s).tapes 18 = BitTape.atEnd archive :=
    (hlother 18 (by decide) (by decide)).trans hlog
  obtain ⟨t, ht, htpc, hthead, htlog, htready, htframe⟩ :=
    LogEntries.steps entries entries.length.bits (preceding ++ Codec.nat entries.length)
      suffix archive tape (loopStart s) rfl hlhead (addressValue_bits entries.length)
      hlword hlready hllog
  have hli : (preceding ++ Codec.nat entries.length) ++ (LogEntries.records entries ++ suffix) = input := by
    simp [input, Codec.list, LogEntries.records, List.append_assoc]
  rw [hli] at ht
  have hl := loop_contains.call input tape ht (by
    simpa [LogEntries.program, htpc] using CountedLoop.exit_instruction LogEntry.program)
  refine ⟨{t with pc := 275}, ?_, rfl, ?_, htlog, htready, ?_⟩
  · change PricedSteps (program.next input tape) _ initial _
    convert ((hp.trans (reset_block input tape s hscount)).trans hr).trans hl using 1
    dsimp [price]
    omega
  · simp only [loopStart, Rewind.finish, resetState] at hthead
    simp only [Codec.list, List.length_append]
    dsimp only [LogEntries.records] at hthead
    omega
  · refine ⟨htframe.1.trans hframe.1, htframe.2.1.trans hframe.2.1,
      htframe.2.2.1.trans hframe.2.2.1, htframe.2.2.2.1.trans hframe.2.2.2.1, ?_⟩
    intro i h10 h12 h13 h14 h15 h16 h18
    exact (htframe.2.2.2.2 i h10 h12 h13 h14 h15 h16 h18).trans (hlother i h10 h14)

theorem run (entries : List LogEntries.Entry) (preceding suffix archive : List Bool)
    (tape : ℕ → Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hready : LogEntry.Ready initial)
    (hcounter : initial.tapes 14 = BitTape.blank)
    (hlog : initial.tapes 18 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      (runPriced (program.next
        (preceding ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)) tape)
        (price entries + 1) initial).finished = some final ∧
      (runPriced (program.next
        (preceding ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)) tape)
        (price entries + 1) initial).instructions = price entries ∧
      final.inputHead = initial.inputHead + (Codec.list LogEntries.encodeEntry entries).length ∧
      final.tapes 18 = BitTape.atEnd (archive ++ LogEntries.records entries) ∧
      LogEntry.Ready final ∧ LogEntries.Frame initial final := by
  obtain ⟨final, hf, hfpc, hh, hl, hr, hframe⟩ :=
    steps entries preceding suffix archive tape initial hpc hhead hready hcounter hlog
  obtain ⟨hfinished, hcost⟩ := hf.runPriced (by simp [BitRAM.next, hfpc, halt_instruction])
  exact ⟨final, hfinished, hcost, hh, hl, hr, hframe⟩

theorem price_le (entries : List LogEntries.Entry) :
    price entries ≤ 21 * entries.length.bits.length + 16 +
      (entries.length + 1) * (13 * entries.length.bits.length + 13) +
      34 * (LogEntries.records entries).length := by
  have h := LogEntries.price_le entries.length.bits entries
  dsimp [price]
  omega

theorem source_entry_list (S : Source.SparseSystem) :
    Codec.list LogEntries.encodeEntry (Codec.sourceRecord S).entries =
      Codec.list (Codec.sourceEntry S) (Codec.sourceEntries S).attach := by
  simp only [Codec.list]
  rw [show (Codec.sourceRecord S).entries.length = (Codec.sourceEntries S).attach.length by
    simp [Codec.sourceRecord]]
  rw [← LogEntries.source_record_bits S]
  rfl

end Maxwell.Cost.ParseEntries
