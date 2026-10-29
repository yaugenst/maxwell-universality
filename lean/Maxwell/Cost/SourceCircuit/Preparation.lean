import Maxwell.Cost.NormalizeSource.Bounds
import Maxwell.Cost.SourceCircuit.InitializeBounds
import Maxwell.Cost.NormalizedRecordParser

namespace Maxwell.Cost.SourceCircuit.Preparation
open Structured
open RationalAccumulator (Blank Word word_of_eq blank_of_eq)

def code (k c : ℕ) : Code := .seq (NormalizeSource.code k c)
  (.seq Initialize.code NormalizedRecordParser.rewindCode)

def archive (S : Source.SparseSystem) (p : ℕ) : List Bool :=
  (Logical.CachedNormalization.sourceTerms S p).flatMap NormalizeSource.termWire

noncomputable def price (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  let precision := Realization.binaryCoefficientPrecision S.nnz k c
  NormalizeSource.price p S k c + Initialize.price S.n S.nnz precision+
    (4*(archive S precision).length+6)

def work : Finset ℕ := NormalizeSource.normalizationTapes ∪ InitializeMetadata.work ∪ {85}

structure Result (S : Source.SparseSystem) (p : ℕ) (data : RootInitData S.n) (s : BitRAMState) : Prop where
  compiler : Initialize.Result S.n S.nnz p data s
  dimension : Word s 19 S.n
  count : Word s 79 S.nnz
  matrixNumerator : Word s 80 (NormalizeRatio.matrixScalePair S).1
  matrixDenominator : Word s 81 (NormalizeRatio.matrixScalePair S).2
  sourceNumerator : Word s 86 (NormalizeRatio.sourceScalePair S).1
  sourceDenominator : Word s 87 (NormalizeRatio.sourceScalePair S).2
  precisionWord : Word s 84 p
  power : Word s 82 (2^p)
  matrixArchive : s.tapes 85 = BitTape.ofList (archive S p)
  sourceArchive : s.tapes 88 = BitTape.atEnd (NormalizeSource.sourceNumeratorWire S p)
  markers : s.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false (Codec.sourceRecord S).entries)
  parser : LogEntry.Ready s
  coefficient : Blank s 83
  inputHead : s.inputHead = (Codec.source S).length
  randomCursor : s.randomCursor = 0
  output : s.output = []
  fresh : ∀ i, 10 ≤ i → i ∉ work → s.tapes i = BitTape.blank

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- Canonical input bytes alone initialize the actual compiler, including
its normalized record tape, precision, binary counters and root array. -/
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t data, Executes (Codec.source S) tape (code k c) cost
        (Store.ofState BitRAMState.initial) t ∧ cost ≤ price p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) data t.val := by
  let precision := Realization.binaryCoefficientPrecision S.nnz k c
  obtain ⟨nc,n,hnc,en,hn⟩ := NormalizeSource.executes p S hp hm hb k c tape
  have hblank (i : ℕ) (hi : i ∉ NormalizeSource.normalizationTapes) : Blank n.val i :=
    ⟨0,hn.fresh i hi⟩
  have hs : BankArray.Scratch n.val :=
    ⟨hn.ready.scratch.1,(RationalAccumulator.zero_word_iff_blank _ _).mp hn.ready.scratch.2.1,
      hn.ready.scratch.2.2.1,hn.ready.scratch.2.2.2,
      hblank 5 (by decide),hblank 6 (by decide),hblank 8 (by decide),hblank 9 (by decide)⟩
  have haux (i : ℕ) (hi : i ∈ InitializeMetadata.banks) : Blank n.val i := by
    apply hblank i
    exact (Finset.disjoint_left.mp (show Disjoint InitializeMetadata.banks
      NormalizeSource.normalizationTapes by decide)) hi
  obtain ⟨ic,r,data,er,hic,hr,fr⟩ := Initialize.executes (Codec.source S) tape S.n S.nnz precision
    (Source.dimension_le_nnz S hp.1) n hn.dimension hn.count hn.precisionWord hs (hblank 7 (by decide)) haux
  have hr85 : r.val.tapes 85 = BitTape.atEnd (archive S precision) :=
    (fr.tapes 85 (by decide) (by decide)).trans hn.matrixArchive
  obtain ⟨t,et,ht85,hti,ft⟩ := NormalizedRecordParser.rewind_executes (Codec.source S) tape
    (archive S precision) r hr85
  have tr (i : ℕ) (hi : i ≠ 85) : t.val.tapes i = r.val.tapes i := ft.tapes i (by simpa using hi)
  have tn (i : ℕ) (hi : i = 4 ∨ 10 ≤ i) (h85 : i ≠ 85)
      (hw : i ∉ InitializeMetadata.work) : t.val.tapes i = n.val.tapes i :=
    (tr i h85).trans (fr.tapes i hi hw)
  refine ⟨_,t,data,en.seq (er.seq et),by dsimp [price,precision] at hic ⊢; omega,?_⟩
  refine ⟨?_,word_of_eq (tn 19 (by decide) (by decide) (by decide)) hn.dimension,
    word_of_eq (tn 79 (by decide) (by decide) (by decide)) hn.count,
    word_of_eq (tn 80 (by decide) (by decide) (by decide)) hn.matrixNumerator,
    word_of_eq (tn 81 (by decide) (by decide) (by decide)) hn.matrixDenominator,
    word_of_eq (tn 86 (by decide) (by decide) (by decide)) hn.sourceNumerator,
    word_of_eq (tn 87 (by decide) (by decide) (by decide)) hn.sourceDenominator,
    word_of_eq (tn 84 (by decide) (by decide) (by decide)) hn.precisionWord,
    word_of_eq (tn 82 (by decide) (by decide) (by decide)) hn.power,
    ht85,(tn 88 (by decide) (by decide) (by decide)).trans hn.sourceArchive,
    (tn 24 (by decide) (by decide) (by decide)).trans hn.markers,?_,
    blank_of_eq (tn 83 (by decide) (by decide) (by decide)) hn.ready.coefficient,
    hti.trans (fr.inputHead.trans hn.inputHead),
    ft.randomCursor.trans (fr.randomCursor.trans hn.randomCursor),
    ft.output.trans (fr.output.trans hn.output),?_⟩
  · refine ⟨InitializeMetadata.scratch_transport hr.scratch (fun i hi => tr i (by omega)),
      blank_of_eq (tr 7 (by decide)) hr.seven,blank_of_eq (tr 37 (by decide)) hr.temporary,
      word_of_eq (tr 90 (by decide)) hr.widthWord,word_of_eq (tr 92 (by decide)) hr.zeroBase,
      BankArray.word_of_eq (tr 91 (by decide)) hr.indexWord,hr.indexLength,hr.indexValue,
      word_of_eq (tr 93 (by decide)) hr.clock,BankArray.word_of_eq (tr 95 (by decide)) hr.next,
      word_of_eq (tr 100 (by decide)) hr.counter,?_,hr.roots⟩
    simpa only [ft.memory] using hr.array
  · exact ⟨(tn 10 (by decide) (by decide) (by decide)).trans hn.ready.parser.1,
      (tn 15 (by decide) (by decide) (by decide)).trans hn.ready.parser.2.1,
      (tn 16 (by decide) (by decide) (by decide)).trans hn.ready.parser.2.2.1,
      (tn 12 (by decide) (by decide) (by decide)).trans hn.ready.parser.2.2.2.1,
      (tn 13 (by decide) (by decide) (by decide)).trans hn.ready.parser.2.2.2.2⟩
  · intro i hi hw
    simp only [work,Finset.mem_union,Finset.mem_singleton,not_or] at hw
    exact (tn i (Or.inr hi) hw.2 hw.1.2).trans (hn.fresh i hw.1.1)

end Maxwell.Cost.SourceCircuit.Preparation
