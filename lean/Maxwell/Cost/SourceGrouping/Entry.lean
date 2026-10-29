import Maxwell.Cost.SourceGrouping.Boundary
import Maxwell.Cost.LogEntry

namespace Maxwell.Cost.SourceGrouping.Entry

/-- Parse one sparse record, append its row boundary, then execute the
existing proved record logger at its literal logging entry point. -/
def program : BitRAM := ⟨
  ParseEntry.program.code.map (BitRAMInstruction.relocate 0 84) ++
  Boundary.program.code.map (BitRAMInstruction.relocate 84 135) ++ [.jump 220] ++
  LogEntry.program.code.map (BitRAMInstruction.relocate 136 368) ++ [.halt]⟩

theorem parse_contains : program.Contains ParseEntry.program 0 84 := by decide
theorem boundary_contains : program.Contains Boundary.program 84 135 := by decide
set_option maxRecDepth 8192 in
theorem log_contains : program.Contains LogEntry.program 136 368 := by decide
theorem jump_instruction : program.code[135]? = some (.jump 220) := by decide
theorem halt_instruction : program.code[368]? = some .halt := by decide

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 15 → i ≠ 16 → i ≠ 18 → i ≠ 22 → i ≠ 24 →
    t.tapes i = s.tapes i)

theorem steps (row column : ℕ) (value : ℚ) (previous : List Bool)
    (preceding suffix archive boundaries : List Bool) (tape : ℕ → Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hready : LogEntry.Ready initial)
    (hlog : initial.tapes 18 = BitTape.atEnd archive)
    (hprevious : initial.tapes 22 = BitTape.atEnd previous)
    (hboundaries : initial.tapes 24 = BitTape.atEnd boundaries) :
    ∃ (cost : ℕ) (final : BitRAMState),
      cost ≤ 75 * LogEntry.width row column value + 30 * previous.length + 230 ∧
      PricedSteps (program.next (preceding ++ (ParseEntry.encode row column value ++ suffix)) tape)
        cost initial final ∧
      final.pc = 368 ∧ final.inputHead = initial.inputHead + (ParseEntry.encode row column value).length ∧
      final.tapes 18 = BitTape.atEnd (archive ++ ParseEntry.encode row column value) ∧
      final.tapes 22 = BitTape.atEnd row.bits ∧
      final.tapes 24 = BitTape.atEnd
        (boundaries ++ [!((row.bits == previous) && initial.registers 33)]) ∧
      final.registers 33 = true ∧ LogEntry.Ready final ∧ Frame initial final := by
  let input := preceding ++ (ParseEntry.encode row column value ++ suffix)
  obtain ⟨p, hp, hppc, hphead, hpcount, hprow, hpcol, hpnum, hpden, hpsign, hpf⟩ :=
    ParseEntry.steps row column value preceding suffix tape initial hpc hhead
      hready.1 hready.2.1 hready.2.2.1 hready.2.2.2.1 hready.2.2.2.2
  have hp' := parse_contains.call input tape hp (by simpa [hppc] using
    (show ParseEntry.program.code[83]? = some .halt by decide))
  simp only [BitRAMState.relocate_zero] at hp'
  have hpother (i : ℕ) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h15 : i ≠ 15) (h16 : i ≠ 16) : p.tapes i = initial.tapes i :=
    hpf.2.2.2.2.1 i h10 h12 h13 h15 h16
  obtain ⟨c, b, hc, hb, hbpc, hbrow, hbprevious, hbarchive, hbseen, hbf⟩ :=
    Boundary.simulation input tape row.bits previous boundaries {p with pc := 0} rfl hprow
      ((hpother 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hprevious)
      ((hpother 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hboundaries)
  have hb' := boundary_contains.call input tape hb (by simpa [hbpc] using Boundary.halt_instruction)
  have hbother (i : ℕ) (h15 : i ≠ 15) (h22 : i ≠ 22) (h24 : i ≠ 24) :
      b.tapes i = p.tapes i := hbf.2.2.2.2.2.2 i h15 h22 h24
  have hl := LogEntry.logging_steps input tape row column value archive b
    ((hbother 10 (by decide) (by decide) (by decide)).trans hpcount) hbrow
    ((hbother 16 (by decide) (by decide) (by decide)).trans hpcol)
    ((hbother 12 (by decide) (by decide) (by decide)).trans hpnum)
    ((hbother 13 (by decide) (by decide) (by decide)).trans hpden)
    (hbf.2.2.2.2.2.1.trans hpsign)
    ((hbother 18 (by decide) (by decide) (by decide)).trans
      ((hpother 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hlog))
  have hl' := log_contains.call input tape hl (by
    simp [LogEntry.finish, LogEntry.halt_instruction])
  have hj : PricedSteps (program.next input tape) 1 {b with pc := 135} {b with pc := 220} := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, jump_instruction]
  let result := {LogEntry.finish row column value archive b with pc := 368}
  have hlf := LogEntry.finish_frame row column value archive b
  have hpseen : p.registers 33 = initial.registers 33 :=
    hpf.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide)
  refine ⟨45 * LogEntry.width row column value + c + 170, result, ?_, ?_, rfl,
    ?_, LogEntry.finish_log row column value archive b, ?_, ?_, ?_,
    LogEntry.finish_ready row column value archive b, ?_⟩
  · dsimp [LogEntry.width] at *
    omega
  · change PricedSteps (program.next input tape) _ initial result
    convert ((hp'.trans hb').trans hj).trans hl' using 1
    dsimp [LogEntry.width]
    omega
  · exact hbf.2.1.trans hphead
  · exact (hlf.2.2.2.2.1 22 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hbprevious
  · have hh := (hlf.2.2.2.2.1 24 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hbarchive
    simpa [result, hpseen] using hh
  · exact (hlf.2.2.2.2.2 33 (by decide)).trans hbseen
  · refine ⟨hlf.1.trans (hbf.1.trans hpf.1),
      hlf.2.1.trans (hbf.2.2.1.trans hpf.2.1),
      hlf.2.2.1.trans (hbf.2.2.2.1.trans hpf.2.2.1),
      hlf.2.2.2.1.trans (hbf.2.2.2.2.1.trans hpf.2.2.2.1), ?_⟩
    intro i h10 h12 h13 h15 h16 h18 h22 h24
    exact (hlf.2.2.2.2.1 i h10 h12 h13 h15 h16 h18).trans
      ((hbother i h15 h22 h24).trans (hpother i h10 h12 h13 h15 h16))

end Maxwell.Cost.SourceGrouping.Entry
