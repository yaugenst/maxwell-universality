import Maxwell.Cost.NormalizeSource.SourceData
import Maxwell.Cost.NormalizeSource.MatrixPass
import Maxwell.Cost.SourceMetadata
import Maxwell.Cost.SourceReplay

namespace Maxwell.Cost.NormalizeSource
open Structured RationalAccumulator
open Logical.Normalization

/-- The fixed encoder frontend: parse and measure the actual source,
construct scale and precision, physically replay its wire, then normalize
its stored coefficients. Its code depends only on fixed promise exponents. -/
def frontendCode (k c : ℕ) : Code := .seq MagnitudeMax.Both.code
  (.seq (SourceMetadata.code k c) (.seq SourceReplay.code matrixPassCode))

/-- The only tapes used before the circuit compiler starts. -/
def frontendTapes : Finset ℕ := MagnitudeMax.Both.work ∪ SourceMetadata.work ∪
  {18,20,74,75} ∪ work

noncomputable def frontendPrice (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  MagnitudeMax.Both.price S (MagnitudeMax.inputWidth p S)+
    SourceMetadata.costBound S.nnz (MagnitudeMax.inputWidth p S) k c+
    SourceReplay.price (Codec.sourceRecord S)+
    matrixPassPrice S.n (Codec.sourceRecord S).entries
      (sourceWidth p S (Realization.binaryCoefficientPrecision S.nnz k c))

structure FrontendState (S : Source.SparseSystem) (precision : ℕ) (t : BitRAMState) : Prop where
  ready : Ready t
  dimension : Word t 19 S.n
  count : Word t 79 S.nnz
  matrixNumerator : Word t 80 (NormalizeRatio.matrixScalePair S).1
  matrixDenominator : Word t 81 (NormalizeRatio.matrixScalePair S).2
  sourceNumerator : Word t 86 (NormalizeRatio.sourceScalePair S).1
  sourceDenominator : Word t 87 (NormalizeRatio.sourceScalePair S).2
  precisionWord : Word t 84 precision
  power : Word t 82 (2^precision)
  archive : t.tapes 85 = BitTape.atEnd
    ((Logical.CachedNormalization.sourceTerms S precision).flatMap termWire)
  markers : t.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false (Codec.sourceRecord S).entries)
  inputHead : t.inputHead =
    (Codec.nat S.n ++ Codec.list LogEntries.encodeEntry (Codec.sourceRecord S).entries).length
  rhsCounter : t.tapes 76 = BitTape.blank
  rhsArchive : t.tapes 88 = BitTape.blank
  randomCursor : t.randomCursor = 0
  output : t.output = []
  fresh : ∀ i ∉ frontendTapes, t.tapes i = BitTape.blank

set_option maxHeartbeats 1000000 in
/-- A complete executed frontend from the canonical source bytes to the
actual compiler coefficient stream. No parsed maxima, normalized values,
precision or input position is supplied as a machine oracle. -/
theorem frontend_executes_with_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ frontendPrice p S k c ∧
      Executes (Codec.source S) tape (frontendCode k c) cost (Store.ofState BitRAMState.initial) t ∧
      FrontendState S (Realization.binaryCoefficientPrecision S.nnz k c) t.val ∧
      t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  let R := Codec.sourceRecord S
  let B := MagnitudeMax.inputWidth p S
  let precision := Realization.binaryCoefficientPrecision S.nnz k c
  have hB : 1 ≤ B := MagnitudeMax.inputWidth_pos p S
  have hentries := MagnitudeMax.promised_entry_width p S hp
  have hrhs := MagnitudeMax.promised_rhs_width p S hp
  obtain ⟨bcost, b, hbcost, eb, hbhead, hb79, hb80, hb81, hb86, hb87, _, hb19,
      hb18, hb20, hb24, hbscratch, hbparser, hbrandom, hbout, hbbank, hbfree⟩ :=
    MagnitudeMax.Both.executes_record R B hB hentries hrhs [] tape
  have hi : ParseSource.recordWire R ++ [] = Codec.source S := by
    simp [R, ParseSource.source_wire]
  rw [hi] at eb
  have hmaxWidth : (MagnitudeMax.maximum (MagnitudeMax.SourceLoop.values R.entries)).1.bits.length ≤ B ∧
      (MagnitudeMax.maximum (MagnitudeMax.SourceLoop.values R.entries)).2.bits.length ≤ B := by
    apply MagnitudeMax.maximum_width _ B B hB
    · intro q hq
      obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hq
      exact (hentries entry he).2.2.1
    · intro q hq
      obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hq
      exact (hentries entry he).2.2.2
  have hrhsWidth := MagnitudeMax.maximum_width R.rhs B B hB
    (fun q hq => (hrhs q hq).1) (fun q hq => (hrhs q hq).2)
  have haux (i : ℕ) (hi : i ∈ SourceMetadata.auxiliary) : Blank b.val i := by
    refine ⟨0, ?_⟩
    exact hbfree i ((Finset.disjoint_left.mp (show Disjoint SourceMetadata.auxiliary MagnitudeMax.Both.work by decide)) hi)
  obtain ⟨mcost, m, hmcost, em, hm80, hm84, hm82, hmbank, hmscratch, hm83, _, hmf⟩ :=
    SourceMetadata.executes R.entries.length
      (MagnitudeMax.maximum (MagnitudeMax.SourceLoop.values R.entries)).1 B k c
      (MagnitudeMax.maximum R.rhs) hmaxWidth.1 hrhsWidth (Codec.source S) tape b
      hb79 hb80 hbbank hbscratch haux
  have hlength : R.entries.length = S.nnz := by simp [R, Codec.sourceRecord, Codec.sourceEntries_length]
  have hmatrixvals : MagnitudeMax.SourceLoop.values R.entries = matrixValues S := MagnitudeMax.source_values S
  rw [hlength, hmatrixvals] at hm80
  rw [hmatrixvals] at hb81
  rw [hlength] at hm82 hm84 hmcost
  have hmhead : m.val.inputHead = (ParseSource.recordWire R).length := hmf.inputHead.trans hbhead
  have hm19 : Word m.val 19 R.dimension := word_of_eq (hmf.tapes 19 (by decide))
    ⟨0, by simpa [BitTape.ofList, BitTape.shifted] using hb19⟩
  have hm79 := word_of_eq (hmf.tapes 79 (by decide)) hb79
  obtain ⟨r, er, hrhead, _, hr20, hrf⟩ := SourceReplay.executes R (by simp [R, Codec.sourceRecord])
    (Codec.source S) tape m hmhead hm19 hm79
    ((hmf.tapes 18 (by decide)).trans hb18) ((hmf.tapes 20 (by decide)).trans hb20)
  have mrkeep (i : ℕ) (h18 : i ≠ 18) (h20 : i ≠ 20) : r.val.tapes i = m.val.tapes i := hrf.tapes i h18 h20
  have brkeep (i : ℕ) (h18 : i ≠ 18) (h20 : i ≠ 20) (hi : i ∉ SourceMetadata.work) :
      r.val.tapes i = b.val.tapes i := (mrkeep i h18 h20).trans (hmf.tapes i hi)
  have rfree (i : ℕ) (h18 : i ≠ 18) (h20 : i ≠ 20)
      (hi : i ∉ SourceMetadata.work) (hib : i ∉ MagnitudeMax.Both.work) : r.val.tapes i = BitTape.blank :=
    (brkeep i h18 h20 hi).trans (hbfree i hib)
  have rready : Ready r.val := by
    refine ⟨?_, ?_, ⟨0, rfree 4 (by decide) (by decide) (by decide) (by decide)⟩,
      blank_of_eq (mrkeep 83 (by decide) (by decide)) hm83, ?_⟩
    · intro i hi hj
      exact word_of_eq (mrkeep i (by omega) (by omega)) (hmbank i hi hj)
    · exact ⟨blank_of_eq (mrkeep 0 (by decide) (by decide)) hmscratch.1,
        word_of_eq (mrkeep 1 (by decide) (by decide)) hmscratch.2.1,
        blank_of_eq (mrkeep 2 (by decide) (by decide)) hmscratch.2.2.1,
        blank_of_eq (mrkeep 3 (by decide) (by decide)) hmscratch.2.2.2⟩
    · exact ⟨(brkeep 10 (by decide) (by decide) (by decide)).trans hbparser.1,
        (brkeep 15 (by decide) (by decide) (by decide)).trans hbparser.2.1,
        (brkeep 16 (by decide) (by decide) (by decide)).trans hbparser.2.2.1,
        (brkeep 12 (by decide) (by decide) (by decide)).trans hbparser.2.2.2.1,
        (brkeep 13 (by decide) (by decide) (by decide)).trans hbparser.2.2.2.2⟩
  have rscale : Word r.val 80 (NormalizeRatio.matrixScalePair S).1 := by
    have hh := word_of_eq (mrkeep 80 (by decide) (by decide)) hm80
    simpa [NormalizeRatio.matrixScalePair] using hh
  have rden : Word r.val 81 (NormalizeRatio.matrixScalePair S).2 := by
    have hh := word_of_eq (brkeep 81 (by decide) (by decide) (by decide)) hb81
    simpa [R, MagnitudeMax.source_values, NormalizeRatio.matrixScalePair] using hh
  have rpower : Word r.val 82 (2^precision) := by
    have hh := word_of_eq (mrkeep 82 (by decide) (by decide)) hm82
    simpa [R, Codec.sourceRecord, Codec.sourceEntries_length, precision] using hh
  have rprecision : Word r.val 84 precision := by
    have hh := word_of_eq (mrkeep 84 (by decide) (by decide)) hm84
    simpa [R, Codec.sourceRecord, Codec.sourceEntries_length, precision] using hh
  have rarchive : r.val.tapes 85 = BitTape.atEnd [] := by
    simpa only [BitTape.atEnd_nil] using rfree 85 (by decide) (by decide) (by decide) (by decide)
  have hs : 1 ≤ precision := by dsimp [precision, Realization.binaryCoefficientPrecision]; omega
  have hpositive := NormalizeRatio.matrixScalePair_positive S (by omega)
  obtain ⟨acost, t, hacost, et, hthead, htlog, htready, htmemory, htrandom, htout, htkeep⟩ :=
    matrixPass_executes S.n R.entries (NormalizeRatio.matrixScalePair S).1
      (NormalizeRatio.matrixScalePair S).2 precision (sourceWidth p S precision) hpositive.1 hpositive.2
      (source_width p S hp hm precision hs) (Codec.vector S.source) [] tape r hrhead rready
      (rfree 74 (by decide) (by decide) (by decide) (by decide))
      (rfree 75 (by decide) (by decide) (by decide) (by decide)) rscale rden rpower rarchive
  have hinput : Codec.nat S.n ++ (Codec.list LogEntries.encodeEntry R.entries ++ Codec.vector S.source) = Codec.source S := by
    simpa [R, ParseSource.recordWire, Codec.vector, Codec.sourceRecord, List.append_assoc] using
      ParseSource.source_wire S
  rw [hinput] at et
  have tk (i : ℕ) (h74 : i ≠ 74) (h75 : i ≠ 75) (hi : i ∉ work) : t.val.tapes i = r.val.tapes i :=
    htkeep i h74 h75 hi
  refine ⟨_, t, ?_, eb.seq (em.seq (er.seq et)), ?_⟩
  · change _ ≤ MagnitudeMax.Both.recordPrice R B + SourceMetadata.costBound S.nnz B k c +
      SourceReplay.price R + matrixPassPrice S.n R.entries (sourceWidth p S precision)
    omega
  · refine ⟨?_, ?_⟩
    swap
    · exact (tk 20 (by decide) (by decide) (by decide)).trans hr20
    refine ⟨htready, ?_, ?_, word_of_eq (tk 80 (by decide) (by decide) (by decide)) rscale,
      word_of_eq (tk 81 (by decide) (by decide) (by decide)) rden, ?_, ?_,
      word_of_eq (tk 84 (by decide) (by decide) (by decide)) rprecision,
      word_of_eq (tk 82 (by decide) (by decide) (by decide)) rpower, ?_, ?_, hthead,
      ?_, ?_, htrandom.trans (hrf.randomCursor.trans (hmf.randomCursor.trans hbrandom)),
      htout.trans (hrf.output.trans (hmf.output.trans hbout)), ?_⟩
    · exact word_of_eq ((tk 19 (by decide) (by decide) (by decide)).trans (mrkeep 19 (by decide) (by decide))) hm19
    · have hh := word_of_eq ((tk 79 (by decide) (by decide) (by decide)).trans (mrkeep 79 (by decide) (by decide))) hm79
      simpa [R, Codec.sourceRecord, Codec.sourceEntries_length] using hh
    · exact word_of_eq ((tk 86 (by decide) (by decide) (by decide)).trans
        (brkeep 86 (by decide) (by decide) (by decide))) hb86
    · exact word_of_eq ((tk 87 (by decide) (by decide) (by decide)).trans
        (brkeep 87 (by decide) (by decide) (by decide))) hb87
    · simpa only [List.nil_append, R, source_records] using htlog
    · exact ((tk 24 (by decide) (by decide) (by decide)).trans
        (brkeep 24 (by decide) (by decide) (by decide))).trans hb24
    · exact (tk 76 (by decide) (by decide) (by decide)).trans
        (rfree 76 (by decide) (by decide) (by decide) (by decide))
    · exact (tk 88 (by decide) (by decide) (by decide)).trans
        (rfree 88 (by decide) (by decide) (by decide) (by decide))
    · intro i hi
      simp only [frontendTapes, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hi
      exact (tk i hi.1.2.2.2.1 hi.1.2.2.2.2 hi.2).trans
        (rfree i hi.1.2.1 hi.1.2.2.1 hi.1.1.2 hi.1.1.1)


/-- The original frontend interface, with the exact RHS archive retained by
`frontend_executes_with_rhs` for source-preserving consumers. -/
theorem frontend_executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ frontendPrice p S k c ∧
      Executes (Codec.source S) tape (frontendCode k c) cost (Store.ofState BitRAMState.initial) t ∧
      FrontendState S (Realization.binaryCoefficientPrecision S.nnz k c) t.val := by
  obtain ⟨cost,t,hcost,he,ht,_⟩ := frontend_executes_with_rhs p S hp hm k c tape
  exact ⟨cost,t,hcost,he,ht⟩

end Maxwell.Cost.NormalizeSource
