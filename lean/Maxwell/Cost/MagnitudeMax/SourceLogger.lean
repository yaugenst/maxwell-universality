import Maxwell.Cost.LogEntry
import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.MagnitudeMax.SourceLogger

open Structured

/-- The fixed logging entry preserves every parsed sparse record. -/
def program : BitRAM := BitRAM.link [.jump 85] LogEntry.program 233 [.halt]

theorem contains : program.Contains LogEntry.program 1 233 := by
  intro i
  exact BitRAM.link_lookup [.jump 85] LogEntry.program 233 [.halt] i.val i.isLt

theorem halt_instruction : program.code[233]? = some .halt := by decide

theorem steps (input : List Bool) (tape : ℕ → Bool) (row column : ℕ) (q : ℚ)
    (archive : List Bool) (s : Store)
    (hcount : s.val.tapes 10 = BitTape.beforeEnd [])
    (hrow : s.val.tapes 15 = BitTape.atEnd row.bits)
    (hcolumn : s.val.tapes 16 = BitTape.atEnd column.bits)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.num.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.den.bits)
    (hsign : s.val.registers 23 = decide (q.num < 0))
    (hlog : s.val.tapes 18 = BitTape.atEnd archive) :
    ∃ t : Store, Executes input tape (.call program) (28 * LogEntry.width row column q + 130) s t ∧
      t.val.inputHead = s.val.inputHead ∧
      t.val.tapes 18 = BitTape.atEnd (archive ++ ParseEntry.encode row column q) ∧
      LogEntry.Ready t.val ∧ LogEntry.Frame s.val t.val := by
  have hj : PricedSteps (program.next input tape) 1 s.val {s.val with pc := 85} := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, program, BitRAM.link, s.property]
  have hl := contains.call input tape
    (LogEntry.logging_steps input tape row column q archive s.val hcount hrow hcolumn hnum hden hsign hlog)
    (by simp [LogEntry.finish, LogEntry.halt_instruction])
  let result := {LogEntry.finish row column q archive s.val with pc := 233}
  have he : PricedSteps (program.next input tape) (28 * LogEntry.width row column q + 129) s.val result := by
    convert hj.trans hl using 1
    omega
  refine ⟨Store.ofState result, ?_, rfl, LogEntry.finish_log row column q archive s.val,
    LogEntry.finish_ready row column q archive s.val, LogEntry.finish_frame row column q archive s.val⟩
  exact Executes.call _ _ _ _ he (by simpa [result] using halt_instruction)

end Maxwell.Cost.MagnitudeMax.SourceLogger
