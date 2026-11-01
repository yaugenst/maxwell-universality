import Maxwell.Cost.MagnitudeMax.Both
import Maxwell.Cost.SourceCaseTest
import Maxwell.Cost.Structured.Determinism

/-! The common source parser also computes the actual base-case branch.
All numerical words and archives retain the ordinary parser contract. -/
namespace Maxwell.Cost.MagnitudeMax.Branch
open Structured RationalAccumulator Logical.Normalization

def code : Code := .seq Both.code SourceCaseTest.code
abbrev work : Finset ℕ := Both.work
def recordPrice (R : Codec.SourceRecord) (B : ℕ) : ℕ := Both.recordPrice R B+13
def price (S : Source.SparseSystem) (B : ℕ) : ℕ := recordPrice (Codec.sourceRecord S) B

theorem executes_record (R : Codec.SourceRecord) (B : ℕ) (hB : 1≤B)
    (hentries : ∀p∈R.entries,SourceLoop.Width B p)
    (hrhs : ∀q∈R.rhs,q.num.natAbs.bits.length≤B ∧ q.den.bits.length≤B)
    (suffix : List Bool) (tape : ℕ→Bool) :
    ∃cost,∃t : Store,cost≤recordPrice R B ∧
      Executes (ParseSource.recordWire R++suffix) tape code cost (Store.ofState BitRAMState.initial) t ∧
      t.val.inputHead=(ParseSource.recordWire R).length ∧
      Word t.val 79 R.entries.length ∧
      Word t.val 80 (maximum (SourceLoop.values R.entries)).1 ∧
      Word t.val 81 (maximum (SourceLoop.values R.entries)).2 ∧
      Word t.val 86 (maximum R.rhs).1 ∧ Word t.val 87 (maximum R.rhs).2 ∧
      t.val.registers 90=decide ((maximum R.rhs).1=0) ∧
      t.val.tapes 19=BitTape.ofList R.dimension.bits ∧
      t.val.tapes 18=BitTape.atEnd (LogEntries.records R.entries) ∧
      t.val.tapes 20=BitTape.atEnd (LogRats.records R.rhs) ∧
      t.val.tapes 24=BitTape.atEnd (SourceGrouping.markers [] false R.entries) ∧
      Scratch t.val 0 ∧ LogEntry.Ready t.val ∧ t.val.randomCursor=0 ∧ t.val.output=[] ∧
      Bank t.val (bankOf (maximum R.rhs)) ∧ (∀i∉work,t.val.tapes i=BitTape.blank) ∧
      t.val.registers 1004=decide ((maximum R.rhs).1=0 ∨ R.entries.length≤1) := by
  obtain ⟨c,s,hc,es,head,w79,w80,w81,w86,w87,zero,dim,entries,rhs,markers,
    scratch,ready,random,output,bank,fresh⟩:=Both.executes_record R B hB hentries hrhs suffix tape
  obtain ⟨t,et,flag,frame,test⟩:=SourceCaseTest.executes R.entries.length
    (ParseSource.recordWire R++suffix) tape s w79
  have keep (i : ℕ) : t.val.tapes i=s.val.tapes i:=frame.tapes i (by simp)
  refine ⟨c+13,t,Nat.add_le_add_right hc 13,es.seq et,frame.inputHead.trans head,
    word_of_eq (keep 79) w79,word_of_eq (keep 80) w80,word_of_eq (keep 81) w81,
    word_of_eq (keep 86) w86,word_of_eq (keep 87) w87,test.trans zero,
    (keep 19).trans dim,(keep 18).trans entries,(keep 20).trans rhs,(keep 24).trans markers,
    ?_,?_,frame.randomCursor.trans random,frame.output.trans output,?_,
    fun i hi=>(keep i).trans (fresh i hi),?_⟩
  · exact ⟨blank_of_eq (keep 0) scratch.1,word_of_eq (keep 1) scratch.2.1,
      blank_of_eq (keep 2) scratch.2.2.1,blank_of_eq (keep 3) scratch.2.2.2⟩
  · exact ⟨(keep 10).trans ready.1,(keep 15).trans ready.2.1,(keep 16).trans ready.2.2.1,
      (keep 12).trans ready.2.2.2.1,(keep 13).trans ready.2.2.2.2⟩
  · exact fun i lo hi=>word_of_eq (keep i) (bank i lo hi)
  · simpa only [zero,Bool.decide_or] using flag

theorem branch_condition (p : Source.Parameters) (S : Source.SparseSystem) (hp : Source.Promises p S)
    (tape : ℕ→Bool) (cost : ℕ) (t : Store)
    (run : Executes (Codec.source S) tape code cost (Store.ofState BitRAMState.initial) t) :
    t.val.registers 1004=decide (S.source=0 ∨ S.nnz≤1) := by
  obtain ⟨c,s,_,es,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,flag⟩:=executes_record
    (Codec.sourceRecord S) (inputWidth p S) (inputWidth_pos p S)
    (promised_entry_width p S hp) (promised_rhs_width p S hp) [] tape
  rw [ParseSource.source_wire,List.append_nil] at es
  have same:=(run.deterministic es).2
  rw [same,flag]
  congr 1
  simp only [Codec.sourceRecord,List.length_map,List.length_attach,
    Codec.sourceEntries_length,rhs_maximum_zero_iff]

#print axioms executes_record
#print axioms branch_condition
end Maxwell.Cost.MagnitudeMax.Branch
