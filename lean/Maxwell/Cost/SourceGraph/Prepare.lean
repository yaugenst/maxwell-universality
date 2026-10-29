import Maxwell.Cost.SourceSquare
import Maxwell.Cost.PositiveGraph.Count
import Maxwell.Cost.PositiveGraph.Metadata.Bounds

namespace Maxwell.Cost.SourceGraph.Prepare
open Structured SourceCircuit
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)

def work : Finset ℕ := PositiveGraph.Count.changed ∪ PositiveGraph.Metadata.work
def suffixCode : Code := .seq PositiveGraph.Count.code PositiveGraph.Metadata.code
def code (k c : ℕ) : Code := .seq (SourceSquare.code k c) suffixCode

def suffixPrice (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  let W := InitializeMetadata.width S.nnz p
  let d := (Logical.sourceCircuit S p).size
  let K := (Logical.sourceSquareEntries S p).length
  K*(66*W+12*(W+3)+89)+10+PositiveGraph.Metadata.price W d K

noncomputable def totalBudget (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  SourceSquare.totalBudget p S k c+suffixPrice S (Realization.binaryCoefficientPrecision S.nnz k c)

structure Result (S : Source.SparseSystem) (p : ℕ) (s : Store) : Prop where
  numeric : PositiveGraph.Metadata.Numeric (InitializeMetadata.width S.nnz p)
    (Logical.sourceCircuit S p).size (Logical.sourceSquareEntries S p).length s.val
  clock : ∃ bits, bits.length=InitializeMetadata.width S.nnz p+3 ∧ BankArray.Word s.val 146 bits
  archive : s.val.tapes 110 = BitTape.shifted
    (SparseEmission.entriesWire (InitializeMetadata.width S.nnz p) (Logical.sourceSquareEntries S p))
    (-(SparseEmission.entriesWire (InitializeMetadata.width S.nnz p) (Logical.sourceSquareEntries S p)).length)
  count : Word s.val 116 (Logical.sourceSquareEntries S p).length
  scratch : BankArray.Scratch s.val
  blank7 : Blank s.val 7
  blank37 : Blank s.val 37
  left : s.val.tapes 111 = BitTape.blank
  right : s.val.tapes 112 = BitTape.blank
  saved : ∃ previous : Store, SourceSquare.Result S p previous ∧ BinaryPrecision.Frame work previous.val s.val

theorem Result.fresh {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s)
    (i : ℕ) (hi : 117 ≤ i) (hout : i < 140 ∨ 160 ≤ i) : s.val.tapes i=BitTape.blank := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact (hf.tapes i (by simp [work,PositiveGraph.Count.changed,PositiveGraph.Metadata.work]; omega)).trans
    (hr.fresh i (by omega))

theorem Result.io {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s) :
    s.val.inputHead=(Codec.source S).length ∧ s.val.randomCursor=0 ∧ s.val.output=[] := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact ⟨hf.inputHead.trans hr.io.1,hf.randomCursor.trans hr.io.2.1,hf.output.trans hr.io.2.2⟩

theorem count_bound (S : Source.SparseSystem) (p : ℕ)
    (hd : (Logical.sourceCircuit S p).size < 2^InitializeMetadata.width S.nnz p) :
    (Logical.sourceSquareEntries S p).length < 2^(InitializeMetadata.width S.nnz p+3) := by
  have h := Logical.sourceSquareEntries_length_le S p
  have hp : 0 < 2^InitializeMetadata.width S.nnz p := by positivity
  rw [pow_add]
  norm_num
  nlinarith

set_option maxRecDepth 16384 in
/-- Count the actually emitted entries and construct all graph descriptors
directly from the source compiler's retained words. -/
theorem from_square (S : Source.SparseSystem) (p : ℕ)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : SourceSquare.Result S p s) :
    ∃ cost t, Executes input tape suffixCode cost s t ∧ cost ≤ suffixPrice S p ∧ Result S p t := by
  let W := InitializeMetadata.width S.nnz p
  let d := (Logical.sourceCircuit S p).size
  let K := (Logical.sourceSquareEntries S p).length
  obtain ⟨previous,metadata,pf⟩ := hs.saved
  obtain ⟨co,hco⟩ := metadata.clock
  have s93 : s.val.tapes 93 = BitTape.shifted (AllocateSource.clock S p) co :=
    (pf.tapes 93 (by decide) (by decide)).trans hco
  have hr : PositiveGraph.Count.Ready 0 (AllocateSource.clock S p) co 0 s :=
    ⟨s93,by simpa [BitTape.shifted,BitTape.blank] using hs.fresh 116 (by decide),hs.clean.2.1,hs.clean.2.2.1⟩
  obtain ⟨ccost,a,hca,ea,a110,ar,af⟩ := PositiveGraph.Count.executes input tape W (W+3)
    (Logical.sourceSquareEntries S p) (AllocateSource.clock S p)
    (-(SparseEmission.entriesWire W (Logical.sourceSquareEntries S p)).length) co 0 s
    (AllocateSource.clock_length S p) (count_bound S p hs.room) hr hs.archive
  have frameA : BinaryPrecision.Frame work s.val a.val :=
    ⟨af.address,af.inputHead,af.memory,af.randomCursor,af.output,
      fun i hi => af.tapes i (by simp only [work,Finset.mem_union,not_or] at hi; exact hi.1)⟩
  have keepA (i : ℕ) (hi : i ∉ PositiveGraph.Count.changed) := af.tapes i hi
  have ascratch : BankArray.Scratch a.val := SourceCircuit.scratch_of_tapes hs.scratch (fun i hi =>
    keepA i (by simp [PositiveGraph.Count.changed]; omega))
  obtain ⟨mcost,t,et,hmt,tn,tc,ts,t7,t37,ft⟩ := PositiveGraph.Metadata.executes input tape W d K
    hs.room (AllocateSource.clock S p) (AllocateSource.clock_length S p) a
    (word_of_eq (keepA 90 (by decide)) hs.widthWord)
    (BankArray.word_of_eq (keepA 95 (by decide)) hs.next) ⟨co,ar.clock⟩ ⟨0,ar.counter⟩
    ascratch (blank_of_eq (keepA 7 (by decide)) hs.blank7)
    (blank_of_eq (keepA 37 (by decide)) hs.blank37)
    (fun i hi hj => ⟨0,(keepA i (by simp [PositiveGraph.Count.changed]; omega)).trans (hs.fresh i (by omega))⟩)
  have frame : BinaryPrecision.Frame work s.val t.val := frameA.trans
    (ft.mono (by intro i hi; exact Finset.mem_union_right _ hi))
  refine ⟨ccost+mcost,t,ea.seq et,Nat.add_le_add hca hmt,tn,tc,
    (ft.tapes 110 (by decide)).trans (a110.trans hs.archive),
    word_of_eq (ft.tapes 116 (by decide)) ⟨0,ar.counter⟩,ts,t7,t37,
    (ft.tapes 111 (by decide)).trans ar.left,(ft.tapes 112 (by decide)).trans ar.right,
    ⟨s,hs,frame⟩⟩

set_option maxRecDepth 16384 in
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t, Executes (Codec.source S) tape (code k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ totalBudget p S k c ∧ Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨scost,s,es,hsc,hs⟩ := SourceSquare.executes p S hp hm hb k c tape
  obtain ⟨cost,t,et,hcost,ht⟩ := from_square S _ (Codec.source S) tape s hs
  exact ⟨scost+cost,t,es.seq et,Nat.add_le_add hsc hcost,ht⟩

def program (k c : ℕ) : BitRAM := (code k c).compile

end Maxwell.Cost.SourceGraph.Prepare
