import Maxwell.Cost.NormalizeSource.Frontend
import Maxwell.Cost.NormalizeSource.Rhs
import Maxwell.Cost.NormalizeSource.RhsBounds

namespace Maxwell.Cost.NormalizeSource
set_option maxRecDepth 8192
open Structured RationalAccumulator

/-- The full finite normalization program, independent of the source data. -/
def code (k c : ℕ) : Code := .seq (frontendCode k c) Rhs.code

def program (k c : ℕ) : BitRAM := (code k c).compile

def normalizationTapes : Finset ℕ := frontendTapes ∪ {76} ∪ Rhs.work

noncomputable def price (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  frontendPrice p S k c + Rhs.price (List.ofFn S.source)
    (sourceWidth p S (Realization.binaryCoefficientPrecision S.nnz k c))

def sourceNumeratorWire (S : Source.SparseSystem) (precision : ℕ) : List Bool :=
  (List.ofFn (fun i => (Logical.Rounding.nearest precision
    (Logical.Normalization.normalizedSource S i)).numerator)).flatMap Codec.int

theorem rhs_records (S : Source.SparseSystem) (precision : ℕ) :
    Rhs.records (NormalizeRatio.sourceScalePair S).1 (NormalizeRatio.sourceScalePair S).2 precision
      (List.ofFn S.source) = sourceNumeratorWire S precision := by
  have hn : (List.ofFn fun i => (Logical.Rounding.nearest precision
      (Logical.Normalization.normalizedSource S i)).numerator) =
      (List.ofFn S.source).map (Rhs.numerator (NormalizeRatio.sourceScalePair S).1
        (NormalizeRatio.sourceScalePair S).2 precision) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp [Rhs.numerator, NormalizeRatio.sourceScalePair_value,
      Logical.Normalization.normalizedSource]
  rw [sourceNumeratorWire, hn, List.flatMap_map]
  rfl

/-- The normalized data retained for the actual circuit and physical source
compiler. Both streams have exact wires and share a generated dyadic scale. -/
structure Result (S : Source.SparseSystem) (precision : ℕ) (t : BitRAMState) : Prop where
  ready : Ready t
  dimension : Word t 19 S.n
  count : Word t 79 S.nnz
  matrixNumerator : Word t 80 (NormalizeRatio.matrixScalePair S).1
  matrixDenominator : Word t 81 (NormalizeRatio.matrixScalePair S).2
  sourceNumerator : Word t 86 (NormalizeRatio.sourceScalePair S).1
  sourceDenominator : Word t 87 (NormalizeRatio.sourceScalePair S).2
  precisionWord : Word t 84 precision
  power : Word t 82 (2^precision)
  matrixArchive : t.tapes 85 = BitTape.atEnd
    ((Logical.CachedNormalization.sourceTerms S precision).flatMap termWire)
  sourceArchive : t.tapes 88 = BitTape.atEnd (sourceNumeratorWire S precision)
  markers : t.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false (Codec.sourceRecord S).entries)
  inputHead : t.inputHead = (Codec.source S).length
  randomCursor : t.randomCursor = 0
  output : t.output = []
  fresh : ∀ i ∉ normalizationTapes, t.tapes i = BitTape.blank

/-- From empty machine state and the canonical source serialization, the
same finite program computes both exact normalized streams and all scales. -/
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ price p S k c ∧
      Executes (Codec.source S) tape (code k c) cost (Store.ofState BitRAMState.initial) t ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) t.val := by
  let precision := Realization.binaryCoefficientPrecision S.nnz k c
  let B := sourceWidth p S precision
  let preceding := Codec.nat S.n ++ Codec.list LogEntries.encodeEntry (Codec.sourceRecord S).entries
  obtain ⟨fc, f, hfc, ef, hf⟩ := frontend_executes p S hp hm k c tape
  have hpositive := NormalizeRatio.sourceScalePair_positive S hb
  have hwidth : ∀ q ∈ List.ofFn S.source,
      Rhs.Width (NormalizeRatio.sourceScalePair S).1 (NormalizeRatio.sourceScalePair S).2 precision B q := by
    intro q hq
    refine ⟨source_rhs_width p S hp precision q hq, ?_⟩
    have hh := source_rounded_bits S hb precision q hq
    change (roundedNumerator _ _ _ _).natAbs.bits.length ≤ _
    dsimp [B, sourceWidth]
    omega
  have hready : Rhs.Ready f.val := ⟨hf.ready.bank, hf.ready.scratch, hf.ready.four,
    hf.ready.parser.1, hf.ready.parser.2.2.2.1, hf.ready.parser.2.2.2.2⟩
  obtain ⟨rc, t, hrc, er, hrhead, hrlog, hrready, hrf⟩ := Rhs.executes (List.ofFn S.source)
    (NormalizeRatio.sourceScalePair S).1 (NormalizeRatio.sourceScalePair S).2 precision B
    hpositive.1 hpositive.2 hwidth preceding [] [] tape f hf.inputHead hf.rhsCounter hready
    hf.sourceNumerator hf.sourceDenominator hf.power (by simpa only [BitTape.atEnd_nil] using hf.rhsArchive)
  have hi : preceding ++ (Codec.list Codec.rat (List.ofFn S.source) ++ []) = Codec.source S := by
    simpa [preceding, ParseSource.recordWire, Codec.sourceRecord, List.append_assoc] using ParseSource.source_wire S
  rw [hi] at er
  have keep (i : ℕ) (hi : i ∉ Rhs.work) (h76 : i ≠ 76) : t.val.tapes i = f.val.tapes i := hrf.tapes i h76 hi
  refine ⟨fc+rc, t, Nat.add_le_add hfc hrc, ef.seq er, ?_⟩
  refine ⟨?_, word_of_eq (keep 19 (by decide) (by decide)) hf.dimension,
    word_of_eq (keep 79 (by decide) (by decide)) hf.count,
    word_of_eq (keep 80 (by decide) (by decide)) hf.matrixNumerator,
    word_of_eq (keep 81 (by decide) (by decide)) hf.matrixDenominator,
    word_of_eq (keep 86 (by decide) (by decide)) hf.sourceNumerator,
    word_of_eq (keep 87 (by decide) (by decide)) hf.sourceDenominator,
    word_of_eq (keep 84 (by decide) (by decide)) hf.precisionWord,
    word_of_eq (keep 82 (by decide) (by decide)) hf.power,
    (keep 85 (by decide) (by decide)).trans hf.archive, ?_,
    (keep 24 (by decide) (by decide)).trans hf.markers, ?_,
    hrf.randomCursor.trans hf.randomCursor, hrf.output.trans hf.output, ?_⟩
  · refine ⟨hrready.bank, hrready.scratch, hrready.four,
      blank_of_eq (keep 83 (by decide) (by decide)) hf.ready.coefficient, ?_⟩
    exact ⟨hrready.parser.1, (keep 15 (by decide) (by decide)).trans hf.ready.parser.2.1,
      (keep 16 (by decide) (by decide)).trans hf.ready.parser.2.2.1,
      hrready.parser.2.1, hrready.parser.2.2⟩
  · simpa only [List.nil_append, rhs_records] using hrlog
  · rw [hrhead, hf.inputHead]
    rw [← hi]
    simp [preceding, add_assoc]
  · intro i hi
    simp only [normalizationTapes, Finset.mem_union, Finset.mem_singleton, not_or] at hi
    exact (keep i hi.2 hi.1.2).trans (hf.fresh i hi.1.1)

theorem run (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ final : BitRAMState,
      ((program k c).run (Codec.source S) tape (price p S k c+1)).finished = some final ∧
      ((program k c).run (Codec.source S) tape (price p S k c+1)).instructions ≤ price p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) final := by
  obtain ⟨cost, t, hc, he, hr⟩ := executes p S hp hm hb k c tape
  obtain ⟨hfinish, hcost⟩ := he.compiled_run (price p S k c+1) (by omega)
  refine ⟨t.place (code k c).size, hfinish, (le_of_eq hcost).trans hc, ?_⟩
  exact ⟨⟨hr.ready.bank, hr.ready.scratch, hr.ready.four, hr.ready.coefficient, hr.ready.parser⟩,
    hr.dimension, hr.count, hr.matrixNumerator, hr.matrixDenominator, hr.sourceNumerator,
    hr.sourceDenominator, hr.precisionWord, hr.power, hr.matrixArchive, hr.sourceArchive,
    hr.markers, hr.inputHead, hr.randomCursor, hr.output, hr.fresh⟩

end Maxwell.Cost.NormalizeSource
