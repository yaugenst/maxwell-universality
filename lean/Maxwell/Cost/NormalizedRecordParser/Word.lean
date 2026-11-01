import Maxwell.Cost.NormalizedRecordParser.Header
import Maxwell.Cost.WordTransfer

/-! Parsing a natural from a retained wire leaves the canonical result at
its first bit, ready for the shared arithmetic machines. -/
namespace Maxwell.Cost.NormalizedRecordParser
open Structured
set_option maxHeartbeats 1200000

def readWord (target : ℕ) : Code:=.seq (readNatural target) (.call (Rewind.program target))

theorem readWord_executes (target : ℕ) (h10t : target≠10) (h85t : target≠85)
    (input : List Bool) (tape : ℕ→Bool) (n : ℕ) (preceding suffix : List Bool) (s : Store)
    (source : s.val.tapes 85=cursor (preceding++(Codec.nat n++suffix)) preceding.length)
    (counter : s.val.tapes 10=BitTape.blank) (output : s.val.tapes target=BitTape.blank) :
    ∃cost t,Executes input tape (readWord target) cost s t ∧ cost≤38*n.bits.length+23 ∧
      t.val.tapes 85=cursor (preceding++(Codec.nat n++suffix)) (preceding.length+(Codec.nat n).length) ∧
      t.val.tapes 10=BitTape.blank ∧ t.val.tapes target=BitTape.ofList n.bits ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.registers 23=s.val.registers 23 ∧
      Frame {target,85} s.val t.val:=by
  obtain ⟨c,a,ex,hc,sa,ca,wa,ia,ra,fa⟩:=readNatural_executes target h10t h85t input tape n preceding suffix s source counter output
  have shifted : a.val.tapes target=BitTape.shiftedEnd n.bits 0:=by simpa [BitTape.atEnd,BitTape.shiftedEnd,BitTape.shifted,BitTape.ofList] using wa
  obtain ⟨er,wr⟩:=WordTransfer.rewind_shifted target 0 input tape n.bits a.val a.property shifted
  let t:=Store.ofState (Rewind.finishAt target 0 a.val)
  have e1 : Executes input tape (.call (Rewind.program target)) (4*n.bits.length+6) a t:=
    Executes.call _ _ _ _ er (by simp [Rewind.program,Rewind.finishAt])
  have keep (i : ℕ) (hi : i≠target) : t.val.tapes i=a.val.tapes i:=by simp [t,Store.ofState,Rewind.finishAt,hi]
  refine ⟨c+(4*n.bits.length+6),t,ex.seq e1,by omega,
    (keep 85 h85t.symm).trans sa,(keep 10 h10t.symm).trans ca,?_,ia,?_,?_⟩
  · simpa only [t,Store.ofState,BitTape.shifted_zero] using wr
  · exact ra
  · refine ⟨fa.address,fa.memory,fa.randomCursor,fa.output,?_⟩
    intro i hi
    have hn : i≠target:=by intro he;subst i;exact hi (by simp)
    exact (keep i hn).trans (fa.tapes i hi)

#print axioms readWord_executes
end Maxwell.Cost.NormalizedRecordParser
