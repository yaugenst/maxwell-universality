import Maxwell.Cost.SourceGrouping.Loop
import Maxwell.Cost.ParseEntries

namespace Maxwell.Cost.SourceGrouping.Parse

/-- The count is parsed from the actual stream before the row-grouping
loop. There is no externally supplied record count in the program. -/
def program : BitRAM := ⟨
  (ParseNat.programOn 14).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10] ++
  (Rewind.program 14).code.map (BitRAMInstruction.relocate 20 25) ++
  Loop.program.code.map (BitRAMInstruction.relocate 25 412) ++ [.halt]⟩

theorem header_contains : program.Contains (ParseNat.programOn 14) 0 19 := by decide
theorem rewind_contains : program.Contains (Rewind.program 14) 20 25 := by decide
set_option maxRecDepth 8192 in
theorem loop_contains : program.Contains Loop.program 25 412 := by
  intro i
  exact BitRAM.link_lookup
    ((ParseNat.programOn 14).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10] ++
      (Rewind.program 14).code.map (BitRAMInstruction.relocate 20 25))
    Loop.program 412 [.halt] i.val i.isLt
set_option maxRecDepth 8192 in
theorem halt_instruction : program.code[412]? = some .halt := by
  have hn : (ParseNat.programOn 14).code.length = 19 := rfl
  have hr : (Rewind.program 14).code.length = 5 := rfl
  have hl : Loop.program.code.length = 387 := rfl
  simp [program, hn, hr, hl]

def price (previous : List Bool) (entries : List LogEntries.Entry) : ℕ :=
  21 * entries.length.bits.length + 16 + Loop.price entries.length.bits previous entries

theorem reset_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input tape) 1 {s with pc := 19}
      ((ParseEntries.resetState s).relocate 20) := by
  apply executeInstructions_sound (instructions := 1)
  have h19 : program.code[19]? = some (.tapeRight 10) := by decide
  simp [executeInstructions, BitRAM.next, h19, BitRAMState.setTape, BitRAMState.relocate,
    ParseEntries.resetState, hcount, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

theorem steps (entries : List LogEntries.Entry) (previous : List Bool) (seen : Bool)
    (preceding suffix archive boundaries : List Bool) (tape : ℕ → Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hready : LogEntry.Ready initial)
    (hcounter : initial.tapes 14 = BitTape.blank)
    (hlog : initial.tapes 18 = BitTape.atEnd archive)
    (hprevious : initial.tapes 22 = BitTape.atEnd previous)
    (hboundaries : initial.tapes 24 = BitTape.atEnd boundaries)
    (hseen : initial.registers 33 = seen) :
    ∃ (cost : ℕ) (final : BitRAMState), cost ≤ price previous entries ∧
      PricedSteps (program.next
        (preceding ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)) tape)
        cost initial final ∧ final.pc = 412 ∧
      final.inputHead = initial.inputHead + (Codec.list LogEntries.encodeEntry entries).length ∧
      final.tapes 18 = BitTape.atEnd (archive ++ LogEntries.records entries) ∧
      final.tapes 22 = BitTape.atEnd (lastWord previous entries) ∧
      final.tapes 24 = BitTape.atEnd (boundaries ++ markers previous seen entries) ∧
      final.registers 33 = finalSeen seen entries ∧
      LogEntry.Ready final ∧ Loop.Frame initial final := by
  let input := preceding ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)
  obtain ⟨s, hs, hspc, hshead, hscount, hsout, hframe⟩ :=
    ParseNat.parse_on_steps 14 (by decide) entries.length preceding
      (LogEntries.records entries ++ suffix) tape initial hpc hhead hready.1 hcounter
  have hi : preceding ++ (Codec.nat entries.length ++ (LogEntries.records entries ++ suffix)) = input := by
    simp [input, Codec.list, LogEntries.records, List.append_assoc]
  rw [hi] at hs
  have hp := header_contains.call input tape hs (by
    simp [ParseNat.programOn, BitRAM.renameTapes, ParseNat.program, hspc, BitRAMInstruction.renameTapes])
  simp only [BitRAMState.relocate_zero] at hp
  have hrword : (ParseEntries.resetState s).tapes 14 = BitTape.atEnd entries.length.bits := by
    simpa [ParseEntries.resetState] using hsout
  have hr := rewind_contains.call input tape
    (Rewind.atEnd_steps 14 input tape entries.length.bits (ParseEntries.resetState s) rfl hrword)
    (by simp [Rewind.program, Rewind.finish])
  have hlword : (ParseEntries.loopStart s).tapes 14 = BitTape.ofList entries.length.bits :=
    Rewind.finish_tape 14 entries.length.bits (ParseEntries.resetState s) hrword
  have hlhead : (ParseEntries.loopStart s).inputHead = (preceding ++ Codec.nat entries.length).length := by
    simpa [ParseEntries.loopStart, Rewind.finish, ParseEntries.resetState, hhead] using hshead
  have hlother (i : ℕ) (hi10 : i ≠ 10) (hi14 : i ≠ 14) :
      (ParseEntries.loopStart s).tapes i = initial.tapes i := by
    simpa [ParseEntries.loopStart, Rewind.finish, ParseEntries.resetState, hi10, hi14] using
      hframe.2.2.2.2.1 i hi10 hi14
  have hlready : LogEntry.Ready (ParseEntries.loopStart s) := by
    refine ⟨?_, (hlother 15 (by decide) (by decide)).trans hready.2.1,
      (hlother 16 (by decide) (by decide)).trans hready.2.2.1,
      (hlother 12 (by decide) (by decide)).trans hready.2.2.2.1,
      (hlother 13 (by decide) (by decide)).trans hready.2.2.2.2⟩
    simp [ParseEntries.loopStart, Rewind.finish, ParseEntries.resetState]
  have hlseen : (ParseEntries.loopStart s).registers 33 = seen := by
    have hh := hframe.2.2.2.2.2 33 (by decide) (by decide) (by decide)
    simpa [ParseEntries.loopStart, Rewind.finish, ParseEntries.resetState] using hh.trans hseen
  obtain ⟨c, t, hc, ht, htpc, hthead, htlog, htprevious, htboundaries, htseen, htready, htf⟩ :=
    Loop.steps entries entries.length.bits previous seen (preceding ++ Codec.nat entries.length)
      suffix archive boundaries tape (ParseEntries.loopStart s) rfl hlhead (addressValue_bits entries.length)
      hlword hlready ((hlother 18 (by decide) (by decide)).trans hlog)
      ((hlother 22 (by decide) (by decide)).trans hprevious)
      ((hlother 24 (by decide) (by decide)).trans hboundaries) hlseen
  have hli : (preceding ++ Codec.nat entries.length) ++ (LogEntries.records entries ++ suffix) = input := by
    simp [input, Codec.list, LogEntries.records, List.append_assoc]
  rw [hli] at ht
  have hl := loop_contains.call input tape ht (by
    simpa [Loop.program, htpc] using CountedLoop.exit_instruction Entry.program)
  refine ⟨21 * entries.length.bits.length + 16 + c, {t with pc := 412},
    by dsimp [price]; omega, ?_, rfl, ?_, htlog, htprevious, htboundaries, htseen, htready, ?_⟩
  · change PricedSteps (program.next input tape) _ initial _
    convert ((hp.trans (reset_block input tape s hscount)).trans hr).trans hl using 1
    omega
  · simp only [ParseEntries.loopStart, Rewind.finish, ParseEntries.resetState] at hthead
    simp only [Codec.list, List.length_append]
    dsimp only [LogEntries.records] at hthead
    omega
  · refine ⟨htf.1.trans hframe.1, htf.2.1.trans hframe.2.1,
      htf.2.2.1.trans hframe.2.2.1, htf.2.2.2.1.trans hframe.2.2.2.1, ?_⟩
    intro i h10 h12 h13 h14 h15 h16 h18 h22 h24
    exact (htf.2.2.2.2 i h10 h12 h13 h14 h15 h16 h18 h22 h24).trans (hlother i h10 h14)

/-- One pass over all encoded record bits, with the actual binary count
width charged on each loop iteration. -/
theorem price_le (entries : List LogEntries.Entry) :
    price [] entries ≤ 21 * entries.length.bits.length + 16 +
      (entries.length + 1) * (13 * entries.length.bits.length + 13) +
      53 * (LogEntries.records entries).length := by
  rw [LogEntries.records_length]
  dsimp [price, Loop.price]
  omega

end Maxwell.Cost.SourceGrouping.Parse
