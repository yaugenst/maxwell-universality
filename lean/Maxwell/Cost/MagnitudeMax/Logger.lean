import Maxwell.Cost.LogRat
import Maxwell.Cost.Structured.Correctness

namespace Maxwell.Cost.MagnitudeMax.Logger

open Structured

/-- Invoke the existing finite logger at its proved logging entry point.
The initial jump and the relocated return are both charged. -/
def program : BitRAM :=
  BitRAM.link [.jump 44] LogRat.program 120 [.halt]

theorem contains : program.Contains LogRat.program 1 120 := by
  intro i
  exact BitRAM.link_lookup [.jump 44] LogRat.program 120 [.halt] i.val i.isLt

theorem halt_instruction : program.code[120]? = some .halt := by decide

theorem steps (input : List Bool) (tape : ℕ → Bool) (q : ℚ) (archive : List Bool)
    (s : Store) (hcount : s.val.tapes 10 = BitTape.beforeEnd [])
    (hnum : s.val.tapes 12 = BitTape.atEnd q.num.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.den.bits)
    (hsign : s.val.registers 23 = decide (q.num < 0))
    (hlog : s.val.tapes 20 = BitTape.atEnd archive) :
    ∃ t : Store, Executes input tape (.call program) (28 * LogRat.width q + 68) s t ∧
      t.val.inputHead = s.val.inputHead ∧
      t.val.tapes 20 = BitTape.atEnd (archive ++ Codec.rat q) ∧
      LogRat.Ready t.val ∧ LogRat.Frame s.val t.val := by
  have hj : PricedSteps (program.next input tape) 1 s.val {s.val with pc := 44} := by
    apply executeInstructions_sound (instructions := 1)
    simp [executeInstructions, BitRAM.next, program, BitRAM.link, s.property]
  have hl := contains.call input tape
    (LogRat.logging_steps input tape q archive s.val hcount hnum hden hsign hlog)
    (by simp [LogRat.finish, LogRat.halt_instruction])
  let result := {LogRat.finish q archive s.val with pc := 120}
  have he : PricedSteps (program.next input tape) (28 * LogRat.width q + 67) s.val result := by
    convert hj.trans hl using 1
    omega
  refine ⟨Store.ofState result, ?_, rfl, LogRat.finish_log q archive s.val,
    LogRat.finish_ready q archive s.val, LogRat.finish_frame q archive s.val⟩
  exact Executes.call _ _ _ _ he (by simpa [result] using halt_instruction)

end Maxwell.Cost.MagnitudeMax.Logger
