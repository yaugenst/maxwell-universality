import Maxwell.Cost.MagnitudeMax.Initialize
import Maxwell.Cost.MagnitudeMax.SourceParse
import Maxwell.Cost.ParseSource

namespace Maxwell.Cost.MagnitudeMax.Source

open Structured RationalAccumulator

/-- A single finite source pass computes the coefficient maximum and row
boundaries while preserving dimension, complete entries, and complete RHS. -/
def code : Code := .seq initializeCode
  (.seq (DecoderParser.readNatural 19) (.seq SourceParse.code (.call ParseRats.program)))

def program : BitRAM := code.compile

def recordPrice (R : Codec.SourceRecord) (B : ℕ) : ℕ :=
  4 + (21 * R.dimension.bits.length + 16) + SourceParse.price R.entries B + (ParseRats.price R.rhs + 1)

theorem executes_record (R : Codec.SourceRecord) (B : ℕ) (hB : 1 ≤ B)
    (hwidth : ∀ p ∈ R.entries, SourceLoop.Width B p) (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ recordPrice R B ∧
      Executes (ParseSource.recordWire R ++ suffix) tape code cost (Store.ofState BitRAMState.initial) t ∧
      t.val.inputHead = (ParseSource.recordWire R).length ∧
      Bank t.val (bankOf (maximum (SourceLoop.values R.entries))) ∧ Scratch t.val 0 ∧
      t.val.tapes 19 = BitTape.ofList R.dimension.bits ∧
      t.val.tapes 18 = BitTape.atEnd (LogEntries.records R.entries) ∧
      t.val.tapes 20 = BitTape.atEnd (LogRats.records R.rhs) ∧
      t.val.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false R.entries) ∧
      t.val.randomCursor = 0 ∧ t.val.output = [] ∧ LogEntry.Ready t.val := by
  let input := ParseSource.recordWire R ++ suffix
  let initial := Store.ofState BitRAMState.initial
  let s := initialized initial
  have hs := initialize_executes input tape initial rfl
  have hb0 : Bank initial.val (bankOf (0, 0)) := by
    intro i _ _
    refine ⟨0, ?_⟩
    simp [initial, Store.ofState, BitRAMState.initial, bankOf, BitTape.blank, BitTape.ofList]
  have hsb : Bank s.val (bankOf (0, 1)) := initialized_bank initial hb0
  have hsr : Scratch s.val 0 := by
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [s, initialized, initial, Store.ofState, BitRAMState.initial, BitTape.blank, BitTape.ofList]
  have hsother (i : ℕ) (hi : i ≠ 31) : s.val.tapes i = BitTape.blank :=
    initialized_other initial i hi
  obtain ⟨d, hd, hdhead, hdim, hd10, hdf⟩ := DecoderParser.readNatural_steps 19 (by decide)
    R.dimension [] (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix))
    tape s rfl (hsother 10 (by decide)) (hsother 19 (by decide))
  have hdi : [] ++ (Codec.nat R.dimension ++
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix))) = input := by
    simp [input, ParseSource.recordWire, List.append_assoc]
  rw [hdi] at hd
  have hdother (i : ℕ) (hi : i ≠ 19) : d.val.tapes i = s.val.tapes i :=
    hdf.tapes i (by simpa using hi)
  have hdblank (i : ℕ) (h19 : i ≠ 19) (h31 : i ≠ 31) : d.val.tapes i = BitTape.blank :=
    (hdother i h19).trans (hsother i h31)
  have hdb : Bank d.val (bankOf (0, 1)) := by
    intro i hi hi'
    exact word_of_eq (hdother i (by omega)) (hsb i hi hi')
  have hdr : Scratch d.val 0 :=
    ⟨blank_of_eq (hdother 0 (by decide)) hsr.1, word_of_eq (hdother 1 (by decide)) hsr.2.1,
      blank_of_eq (hdother 2 (by decide)) hsr.2.2.1, blank_of_eq (hdother 3 (by decide)) hsr.2.2.2⟩
  have hdparser : LogEntry.Ready d.val :=
    ⟨hd10, hdblank 15 (by decide) (by decide), hdblank 16 (by decide) (by decide),
      hdblank 12 (by decide) (by decide), hdblank 13 (by decide) (by decide)⟩
  have hdnext : d.val.inputHead = (Codec.nat R.dimension).length := by
    simpa [s, initialized, initial, Store.ofState, BitRAMState.initial] using hdhead
  obtain ⟨ec, e, hec, he, hehead, heb, her, heparser, helog, _, hemarkers, hef⟩ :=
    SourceParse.executes R.entries (0, 1) B (Codec.nat R.dimension)
      (Codec.list Codec.rat R.rhs ++ suffix) [] tape d hdnext (hdblank 14 (by decide) (by decide))
      (by decide) (by simp [hB]) hwidth hdb hdr hdparser
      (by simpa [BitTape.atEnd_nil] using hdblank 18 (by decide) (by decide))
      (by simpa [BitTape.atEnd_nil] using hdblank 22 (by decide) (by decide))
      (by simpa [BitTape.atEnd_nil] using hdblank 24 (by decide) (by decide))
  have hei : Codec.nat R.dimension ++
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix)) = input := by
    simp [input, ParseSource.recordWire, List.append_assoc]
  rw [hei] at he
  have heother (i : ℕ) (h4 : 4 ≤ i) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h14 : i ≠ 14) (h15 : i ≠ 15) (h16 : i ≠ 16) (h18 : i ≠ 18) (h22 : i ≠ 22)
      (h24 : i ≠ 24) (hbank : i < 30 ∨ 36 < i) : e.val.tapes i = d.val.tapes i :=
    hef.2.2.2.2 i h4 h10 h12 h13 h14 h15 h16 h18 h22 h24 hbank
  have henext : e.val.inputHead =
      (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries).length := by
    simpa [hdnext] using hehead
  have he21 : e.val.tapes 21 = BitTape.blank :=
    (heother 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans
      (hdblank 21 (by decide) (by decide))
  have he20 : e.val.tapes 20 = BitTape.atEnd [] := by
    simpa [BitTape.atEnd_nil] using
      (heother 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans
        (hdblank 20 (by decide) (by decide))
  obtain ⟨r, hr, hrpc, hrhead, hrlog, hrparser, hrf⟩ := ParseRats.steps R.rhs
    (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries) suffix [] tape e.val e.property henext
    ⟨heparser.1, heparser.2.2.2.1, heparser.2.2.2.2⟩ he21 he20
  have hri : (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries) ++
      (Codec.list Codec.rat R.rhs ++ suffix) = input := by
    simp [input, ParseSource.recordWire, List.append_assoc]
  rw [hri] at hr
  have hr' : Executes input tape (.call ParseRats.program) (ParseRats.price R.rhs + 1) e (Store.ofState r) :=
    Executes.call _ _ _ _ hr (by simpa [hrpc] using ParseRats.halt_instruction)
  have hrother (i : ℕ) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h21 : i ≠ 21) (h20 : i ≠ 20) : r.tapes i = e.val.tapes i :=
    hrf.2.2.2.2 i h10 h12 h13 h21 h20
  refine ⟨4 + ((21 * R.dimension.bits.length + 16) + (ec + (ParseRats.price R.rhs + 1))),
    Store.ofState r, by dsimp [recordPrice]; omega, hs.seq (hd.seq (he.seq hr')), ?_, ?_, ?_, ?_, ?_,
    by simpa [Store.ofState] using hrlog, (hrother 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hemarkers,
    hrf.2.2.1.trans (hef.2.2.1.trans hdf.randomCursor),
    hrf.2.2.2.1.trans (hef.2.2.2.1.trans hdf.output), ?_⟩
  · simpa [Store.ofState, ParseSource.recordWire, henext, Nat.cast_add, add_assoc] using hrhead
  · intro i hi hi'
    exact word_of_eq (hrother i (by omega) (by omega) (by omega) (by omega) (by omega)) (heb i hi hi')
  · exact ⟨blank_of_eq (hrother 0 (by decide) (by decide) (by decide) (by decide) (by decide)) her.1,
      word_of_eq (hrother 1 (by decide) (by decide) (by decide) (by decide) (by decide)) her.2.1,
      blank_of_eq (hrother 2 (by decide) (by decide) (by decide) (by decide) (by decide)) her.2.2.1,
      blank_of_eq (hrother 3 (by decide) (by decide) (by decide) (by decide) (by decide)) her.2.2.2⟩
  · exact (hrother 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((heother 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hdim)
  · simpa [Store.ofState] using (hrother 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans helog
  · exact ⟨hrparser.1,
      (hrother 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans heparser.2.1,
      (hrother 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans heparser.2.2.1,
      hrparser.2.1, hrparser.2.2⟩

def price (S : Source.SparseSystem) (B : ℕ) : ℕ := recordPrice (Codec.sourceRecord S) B

set_option maxRecDepth 8192 in
/-- Actual capped execution on exactly the canonical sparse-source wire. -/
theorem run (S : Source.SparseSystem) (B : ℕ) (hB : 1 ≤ B)
    (hwidth : ∀ p ∈ (Codec.sourceRecord S).entries, SourceLoop.Width B p)
    (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ final : BitRAMState,
      (program.run (Codec.source S ++ suffix) tape (price S B + 1)).finished = some final ∧
      (program.run (Codec.source S ++ suffix) tape (price S B + 1)).instructions ≤ price S B ∧
      final.inputHead = (Codec.source S).length ∧
      Word final 30 (maximum (SourceLoop.values (Codec.sourceRecord S).entries)).1 ∧
      Word final 31 (maximum (SourceLoop.values (Codec.sourceRecord S).entries)).2 ∧
      final.tapes 19 = BitTape.ofList S.n.bits ∧
      final.tapes 18 = BitTape.atEnd (LogEntries.records (Codec.sourceRecord S).entries) ∧
      final.tapes 20 = BitTape.atEnd (LogRats.records (List.ofFn S.source)) ∧
      final.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false (Codec.sourceRecord S).entries) ∧
      final.randomCursor = 0 ∧ final.output = [] ∧ LogEntry.Ready final := by
  obtain ⟨c, t, hc, ht, hh, hb, _, hd, he, hr, hm, hrandom, hout, hready⟩ :=
    executes_record (Codec.sourceRecord S) B hB hwidth suffix tape
  rw [ParseSource.source_wire] at ht hh
  obtain ⟨hrun, hcost⟩ := ht.compiled_run (price S B + 1) (by exact Nat.lt_succ_of_le hc)
  refine ⟨t.place code.size, hrun, (le_of_eq hcost).trans hc, hh, ?_, ?_, hd, he, hr, hm, hrandom, hout, hready⟩
  · simpa [bankOf, Word, Store.place] using hb 30 (by decide) (by decide)
  · simpa [bankOf, Word, Store.place] using hb 31 (by decide) (by decide)

end Maxwell.Cost.MagnitudeMax.Source
