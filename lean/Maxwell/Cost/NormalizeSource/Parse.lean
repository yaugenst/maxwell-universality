import Maxwell.Cost.ParseEntry
import Maxwell.Cost.LogEntry
import Maxwell.Cost.DecoderParser.Primitives

namespace Maxwell.Cost.NormalizeSource
open Structured

def readEntry : Code := .seq (.call ParseEntry.program) (.call DecoderParser.resetCounter)

theorem readEntry_executes (row column : ℕ) (q : ℚ) (preceding suffix : List Bool)
    (tape : ℕ → Bool) (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hready : LogEntry.Ready s.val) :
    ∃ t : Store, Executes (preceding ++ (ParseEntry.encode row column q ++ suffix)) tape readEntry
      (17*(row.bits.length+column.bits.length+q.num.natAbs.bits.length+q.den.bits.length)+42) s t ∧
      t.val.inputHead = s.val.inputHead+(ParseEntry.encode row column q).length ∧
      t.val.tapes 10 = BitTape.blank ∧
      t.val.tapes 15 = BitTape.atEnd row.bits ∧ t.val.tapes 16 = BitTape.atEnd column.bits ∧
      t.val.tapes 12 = BitTape.atEnd q.num.natAbs.bits ∧ t.val.tapes 13 = BitTape.atEnd q.den.bits ∧
      t.val.registers 23 = decide (q.num < 0) ∧ ParseEntry.Frame s.val t.val := by
  obtain ⟨u, eu, hup, huh, hu10, hu15, hu16, hu12, hu13, hus, huf⟩ :=
    ParseEntry.steps row column q preceding suffix tape s.val s.property hhead
      hready.1 hready.2.1 hready.2.2.1 hready.2.2.2.1 hready.2.2.2.2
  have e1 := Executes.call ParseEntry.program s u _ eu (by rw [hup]; decide)
  have e2 := DecoderParser.resetCounter_steps
    (preceding ++ (ParseEntry.encode row column q ++ suffix)) tape (Store.ofState u) hu10
  let t := Store.ofState (DecoderParser.resetCounterState u)
  refine ⟨t, ?_, huh, ?_, ?_, ?_, ?_, ?_, hus, ?_⟩
  · exact e1.seq e2
  · simp [t, Store.ofState, DecoderParser.resetCounterState]
  · simpa [t, Store.ofState, DecoderParser.resetCounterState] using hu15
  · simpa [t, Store.ofState, DecoderParser.resetCounterState] using hu16
  · simpa [t, Store.ofState, DecoderParser.resetCounterState] using hu12
  · simpa [t, Store.ofState, DecoderParser.resetCounterState] using hu13
  · refine ⟨huf.1, huf.2.1, huf.2.2.1, huf.2.2.2.1, ?_, huf.2.2.2.2.2⟩
    intro i h10 h12 h13 h15 h16
    simpa [t, Store.ofState, DecoderParser.resetCounterState, h10] using
      huf.2.2.2.2.1 i h10 h12 h13 h15 h16

end Maxwell.Cost.NormalizeSource
