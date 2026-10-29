import Maxwell.Cost.SourceCircuit.CompileSource

namespace Maxwell.Cost.SourceCircuit.FinalMetadata
open Structured
open RationalAccumulator (Blank Word word_of_eq blank_of_eq)

/-- Persistent source quantities and clean backend storage at completion of
all actual copy-bank, Horner, and row-reduction instructions. -/
structure Metadata (S : Source.SparseSystem) (precision : ℕ) (s : Store) : Prop where
  scratch : BankArray.Scratch s.val
  blank7 : Blank s.val 7
  blank37 : Blank s.val 37
  dimension : Word s.val 19 S.n
  count : Word s.val 79 S.nnz
  precisionWord : Word s.val 84 precision
  power : Word s.val 82 (2^precision)
  matrixNumerator : Word s.val 80 (NormalizeRatio.matrixScalePair S).1
  matrixDenominator : Word s.val 81 (NormalizeRatio.matrixScalePair S).2
  sourceNumerator : Word s.val 86 (NormalizeRatio.sourceScalePair S).1
  sourceDenominator : Word s.val 87 (NormalizeRatio.sourceScalePair S).2
  sourceArchive : s.val.tapes 88 = BitTape.atEnd (NormalizeSource.sourceNumeratorWire S precision)
  widthWord : Word s.val 90 (InitializeMetadata.width S.nnz precision)
  clock : Word s.val 93 (2^InitializeMetadata.exponent S.nnz precision)
  fresh : ∀ i, 110 ≤ i → s.val.tapes i = BitTape.blank
  inputHead : s.val.inputHead = (Codec.source S).length
  randomCursor : s.val.randomCursor = 0
  output : s.val.output = []

set_option maxRecDepth 8192 in
theorem preserved (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (pre allocated start t : Store)
    (hpre : Preparation.Result S p roots pre.val)
    (ha : AllocateSource.Result S p roots pre.val.memory allocated)
    (fpa : AllocationPass.Persistent pre allocated)
    (fas : BinaryPrecision.Frame ArithmeticPrelude.work allocated.val start.val)
    (fst : ArithmeticPass.Persistent start t)
    (ht : CompileSource.Result S p roots pre.val.memory t) : Metadata S p t := by
  have keep (i : ℕ) (hi : 10 ≤ i) (ha : i ∉ AllocationPass.work)
      (hp : i ∉ ArithmeticPrelude.work) (ht : i ∉ ArithmeticPass.work) :
      t.val.tapes i = pre.val.tapes i :=
    (fst.tapes i (Or.inr hi) ht).trans ((fas.tapes i hp).trans (fpa.tapes i (Or.inr hi) ha))
  obtain ⟨po,oo,ar⟩ := ha.ready
  have t37 : Blank t.val 37 := blank_of_eq
    ((fst.tapes 37 (by decide) (by decide)).trans (fas.tapes 37 (by decide))) ar.blank37
  refine ⟨ht.ready.scratch,ht.ready.blank7,t37,
    word_of_eq (keep 19 (by decide) (by decide) (by decide) (by decide)) hpre.dimension,
    word_of_eq (keep 79 (by decide) (by decide) (by decide) (by decide)) hpre.count,
    word_of_eq (keep 84 (by decide) (by decide) (by decide) (by decide)) hpre.precisionWord,
    word_of_eq (keep 82 (by decide) (by decide) (by decide) (by decide)) hpre.power,
    word_of_eq (keep 80 (by decide) (by decide) (by decide) (by decide)) hpre.matrixNumerator,
    word_of_eq (keep 81 (by decide) (by decide) (by decide) (by decide)) hpre.matrixDenominator,
    word_of_eq (keep 86 (by decide) (by decide) (by decide) (by decide)) hpre.sourceNumerator,
    word_of_eq (keep 87 (by decide) (by decide) (by decide) (by decide)) hpre.sourceDenominator,
    (keep 88 (by decide) (by decide) (by decide) (by decide)).trans hpre.sourceArchive,
    word_of_eq (keep 90 (by decide) (by decide) (by decide) (by decide)) hpre.compiler.widthWord,
    word_of_eq (keep 93 (by decide) (by decide) (by decide) (by decide)) hpre.compiler.clock,?_,
    fst.inputHead.trans (fas.inputHead.trans (fpa.inputHead.trans hpre.inputHead)),
    fst.randomCursor.trans (fas.randomCursor.trans (fpa.randomCursor.trans hpre.randomCursor)),
    fst.output.trans (fas.output.trans (fpa.output.trans hpre.output))⟩
  intro i hi
  have outside (work : Finset ℕ) (bound : ∀ j ∈ work, j < 110) : i ∉ work := by
    intro hmem
    have := bound i hmem
    omega
  exact (keep i (by omega)
    (outside AllocationPass.work (by decide))
    (outside ArithmeticPrelude.work (by decide))
    (outside ArithmeticPass.work (by decide))).trans
    (hpre.fresh i (by omega) (outside Preparation.work (by decide)))

theorem Metadata.backend {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Metadata S p s) :
    s.val.tapes 110 = BitTape.blank ∧ s.val.tapes 111 = BitTape.blank ∧
    s.val.tapes 112 = BitTape.blank ∧ s.val.tapes 113 = BitTape.blank ∧
    s.val.tapes 114 = BitTape.blank ∧ s.val.tapes 115 = BitTape.blank :=
  ⟨h.fresh 110 (by decide),h.fresh 111 (by decide),h.fresh 112 (by decide),
    h.fresh 113 (by decide),h.fresh 114 (by decide),h.fresh 115 (by decide)⟩

end Maxwell.Cost.SourceCircuit.FinalMetadata
