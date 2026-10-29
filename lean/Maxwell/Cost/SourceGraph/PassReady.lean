import Maxwell.Cost.SourceGraph.Retain
import Maxwell.Cost.PositiveGraph.PassBounds
import Maxwell.Cost.PositiveGraph.Invariant.EndpointSource
import Maxwell.Cost.PositiveGraph.Preservation

namespace Maxwell.Cost.SourceGraph.Positive
open Structured SourceCircuit PositiveGraph
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)

def width (S : Source.SparseSystem) (p : ℕ) := InitializeMetadata.width S.nnz p
def dimension (S : Source.SparseSystem) (p : ℕ) := (Logical.sourceCircuit S p).size
def count (S : Source.SparseSystem) (p : ℕ) := (Logical.sourceSquareEntries S p).length
def base (S : Source.SparseSystem) (p : ℕ) :=
  4*count S p*(width S p+3)+2*(2*dimension S p+count S p)+2*(4*count S p)
def initialTables (S : Source.SparseSystem) (p : ℕ) : Tables (dimension S p) (count S p) :=
  ⟨Initialize.constantWords (4*count S p) (width S p+3) 0,
    Initialize.constantWords (2*dimension S p+count S p) 4 8⟩

structure Ready (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState) : Prop where
  room : dimension S p < 2^width S p
  descriptor : ∃ sourceClock endpointClock diagonalClock,
    Descriptor (width S p) (dimension S p) (base S p) sourceClock endpointClock diagonalClock s
  numeric : Metadata.Numeric (width S p) (dimension S p) (count S p) s
  arrays : Initialize.Arrays (width S p) (dimension S p) (count S p) s.memory
  workspace : Workspace s
  left : Blank s 118
  right : Blank s 119
  mediator : Blank s 121
  archive : TapeRepresents (s.tapes 110) (recordsWire (width S p) (Invariant.sourceRecords S p))

theorem from_retained {S : Source.SparseSystem} {p : ℕ} {s : Store}
    (h : Retained.Result S p s) : Ready S p s.val := by
  obtain ⟨initialized,hi,rf⟩ := h.saved
  obtain ⟨prepared,hp,pf⟩ := hi.saved
  obtain ⟨square,hq,qf⟩ := hp.saved
  obtain ⟨compiled,hc,cf⟩ := hq.saved
  obtain ⟨endpointClock,hlen,config⟩ := hi.config
  have keep (i : ℕ) (hi : i ∉ Retain.work) := rf.tapes i hi
  have numeric := config.numeric.transport (fun i hlo hhi _ => keep i (by simp [Retain.work]; omega))
  obtain ⟨origin,hclock⟩ := hc.clock
  have sourceClock : BankArray.Word s.val 93 (AllocateSource.clock S p) :=
    ⟨origin,(keep 93 (by decide)).trans
      ((pf.tapes 93 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((qf.tapes 93 (by decide)).trans ((cf.tapes 93 (by decide) (by decide)).trans hclock)))⟩
  have next : BankArray.Word s.val 95 (fixedWidth (width S p) (dimension S p)) :=
    BankArray.word_of_eq ((keep 95 (by decide)).trans
      ((pf.tapes 95 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (qf.tapes 95 (by decide)))) hq.next
  have descriptor : Descriptor (width S p) (dimension S p) (base S p)
      (AllocateSource.clock S p) endpointClock (8:ℕ).bits s.val :=
    ⟨sourceClock,AllocateSource.clock_length S p,next,numeric.widthWord,
      BankArray.word_of_eq (keep 146 (by decide)) config.clockWord,hlen,
      numeric.endpointBase,numeric.four,numeric.diagonalBase,numeric.clockFour,by decide⟩
  have left : s.val.tapes 111=BitTape.blank := (keep 111 (by decide)).trans
    ((pf.tapes 111 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.left)
  have right : s.val.tapes 112=BitTape.blank := (keep 112 (by decide)).trans
    ((pf.tapes 112 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp.right)
  have archive : TapeRepresents (s.val.tapes 110) (recordsWire (width S p) (Invariant.sourceRecords S p)) := by
    rw [keep 110 (by decide),hi.archive]
    rw [recordsWire,Invariant.sourceRecords_map]
    exact BitTape.shifted_represents _ _
  refine ⟨hq.room,⟨_,_,_,descriptor⟩,numeric,?_,
    ⟨h.scratch,blank_of_eq (keep 7 (by decide)) config.seven,
      blank_of_eq (keep 37 (by decide)) config.temporary,
      ⟨0,h.fresh 120 (by decide) (by decide) (by decide)⟩,
      ⟨0,h.fresh 122 (by decide) (by decide) (by decide)⟩,left,right⟩,
    ⟨0,h.fresh 118 (by decide) (by decide) (by decide)⟩,
    ⟨0,h.fresh 119 (by decide) (by decide) (by decide)⟩,
    ⟨0,h.fresh 121 (by decide) (by decide) (by decide)⟩,archive⟩
  rw [rf.memory]
  exact hi.arrays

end Maxwell.Cost.SourceGraph.Positive
