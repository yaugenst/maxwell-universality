import Maxwell.Cost.MagnitudeMax.Front
import Maxwell.Cost.MagnitudeMax.Tail

namespace Maxwell.Cost.MagnitudeMax.Both

open Structured RationalAccumulator Logical.Normalization

def code : Code := .seq Front.code Tail.code

def program : BitRAM := code.compile

def work : Finset ℕ := Front.work ∪ Tail.work

def recordPrice (R : Codec.SourceRecord) (B : ℕ) : ℕ := Front.price R B + Tail.price R.rhs B

theorem executes_record (R : Codec.SourceRecord) (B : ℕ) (hB : 1 ≤ B)
    (hentries : ∀ p ∈ R.entries, SourceLoop.Width B p)
    (hrhs : ∀ q ∈ R.rhs, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ recordPrice R B ∧
      Executes (ParseSource.recordWire R ++ suffix) tape code cost (Store.ofState BitRAMState.initial) t ∧
      t.val.inputHead = (ParseSource.recordWire R).length ∧
      Word t.val 79 R.entries.length ∧
      Word t.val 80 (maximum (SourceLoop.values R.entries)).1 ∧
      Word t.val 81 (maximum (SourceLoop.values R.entries)).2 ∧
      Word t.val 86 (maximum R.rhs).1 ∧ Word t.val 87 (maximum R.rhs).2 ∧
      t.val.registers 90 = decide ((maximum R.rhs).1 = 0) ∧
      t.val.tapes 19 = BitTape.ofList R.dimension.bits ∧
      t.val.tapes 18 = BitTape.atEnd (LogEntries.records R.entries) ∧
      t.val.tapes 20 = BitTape.atEnd (LogRats.records R.rhs) ∧
      t.val.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false R.entries) ∧
      Scratch t.val 0 ∧ LogEntry.Ready t.val ∧ t.val.randomCursor = 0 ∧ t.val.output = [] ∧
      Bank t.val (bankOf (maximum R.rhs)) ∧ (∀ i ∉ work, t.val.tapes i = BitTape.blank) := by
  obtain ⟨c, s, hc, hs, hhead, hbank, hscratch, hparser, h79, hdim, hlog, hmarkers, hrandom, hout, hfree⟩ :=
    Front.executes R B hB hentries suffix tape
  have hvalues : ∀ q ∈ SourceLoop.values R.entries, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (hentries p hp).2.2
  have hmatrix := maximum_width (SourceLoop.values R.entries) B B hB
    (fun q hq => (hvalues q hq).1) (fun q hq => (hvalues q hq).2)
  have hblank (i : ℕ) (hi : i ∉ Front.work) : Blank s.val i :=
    ⟨0, by simpa [BitTape.blank] using hfree i hi⟩
  obtain ⟨c', t, hc', ht, hthead, ht80, ht81, ht86, ht87, htest, htlog, htr, htp, htf, htb⟩ :=
    Tail.executes (maximum (SourceLoop.values R.entries)) R.rhs B hB hmatrix hrhs
      (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries) suffix tape s hhead
      hbank hscratch ⟨hparser.1, hparser.2.2.2.1, hparser.2.2.2.2⟩
      (by simpa [BitTape.atEnd_nil] using hfree 20 (by decide)) (hfree 21 (by decide))
      (hblank 80 (by decide)) (hblank 81 (by decide)) (hblank 86 (by decide)) (hblank 87 (by decide))
  have hi : (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries) ++
      (Codec.list Codec.rat R.rhs ++ suffix) = ParseSource.recordWire R ++ suffix := by
    simp [ParseSource.recordWire, List.append_assoc]
  rw [hi] at ht
  refine ⟨c + c', t, by dsimp [recordPrice]; omega, hs.seq ht, ?_,
    word_of_eq (htf.tapes 79 (by decide)) h79, ht80, ht81, ht86, ht87, htest,
    (htf.tapes 19 (by decide)).trans hdim, (htf.tapes 18 (by decide)).trans hlog,
    htlog, (htf.tapes 24 (by decide)).trans hmarkers, htr, ?_,
    htf.randomCursor.trans hrandom, htf.output.trans hout, htb, ?_⟩
  · simpa [ParseSource.recordWire, hhead, Nat.cast_add, add_assoc] using hthead
  · exact ⟨htp.1, (htf.tapes 15 (by decide)).trans hparser.2.1,
      (htf.tapes 16 (by decide)).trans hparser.2.2.1, htp.2.1, htp.2.2⟩
  · intro i hi
    simp only [work, Finset.mem_union, not_or] at hi
    exact (htf.tapes i hi.2).trans (hfree i hi.1)

def price (S : Source.SparseSystem) (B : ℕ) : ℕ := recordPrice (Codec.sourceRecord S) B

set_option maxRecDepth 8192 in
/-- Both normalizing maxima, complete sparse metadata, and a zero-RHS
flag are produced by one fixed finite machine on the actual source wire. -/
theorem run (S : Source.SparseSystem) (B : ℕ) (hB : 1 ≤ B)
    (hentries : ∀ p ∈ (Codec.sourceRecord S).entries, SourceLoop.Width B p)
    (hrhs : ∀ q ∈ List.ofFn S.source, q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ final : BitRAMState,
      (program.run (Codec.source S ++ suffix) tape (price S B + 1)).finished = some final ∧
      (program.run (Codec.source S ++ suffix) tape (price S B + 1)).instructions ≤ price S B ∧
      final.inputHead = (Codec.source S).length ∧ Word final 79 S.nnz ∧
      Word final 80 (maximum (matrixValues S)).1 ∧ Word final 81 (maximum (matrixValues S)).2 ∧
      Word final 86 (maximum (List.ofFn S.source)).1 ∧ Word final 87 (maximum (List.ofFn S.source)).2 ∧
      (final.registers 90 = true ↔ S.source = 0) ∧
      final.tapes 19 = BitTape.ofList S.n.bits ∧
      final.tapes 18 = BitTape.atEnd (LogEntries.records (Codec.sourceRecord S).entries) ∧
      final.tapes 20 = BitTape.atEnd (LogRats.records (List.ofFn S.source)) ∧
      final.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false (Codec.sourceRecord S).entries) ∧
      Scratch final 0 ∧ LogEntry.Ready final ∧ final.randomCursor = 0 ∧ final.output = [] ∧
      Bank final (bankOf (maximum (List.ofFn S.source))) ∧ (∀ i ∉ work, final.tapes i = BitTape.blank) := by
  obtain ⟨c, t, hc, ht, hh, hm, ha, hA, hb, hB', hz, hd, he, hr, hmarkers, hscratch, hready, hrandom, hout, hbank, hfree⟩ :=
    executes_record (Codec.sourceRecord S) B hB hentries hrhs suffix tape
  rw [ParseSource.source_wire] at ht hh
  obtain ⟨hrun, hcost⟩ := ht.compiled_run (price S B + 1) (Nat.lt_succ_of_le hc)
  refine ⟨t.place code.size, hrun, (le_of_eq hcost).trans hc, hh, ?_, ?_, ?_, hb, hB', ?_,
    hd, he, hr, hmarkers, hscratch, hready, hrandom, hout, hbank, hfree⟩
  · simpa [Codec.sourceRecord, Codec.sourceEntries_length, Word, Store.place] using hm
  · simpa [source_values, Word, Store.place] using ha
  · simpa [source_values, Word, Store.place] using hA
  · change t.val.registers 90 = true ↔ S.source = 0
    rw [hz]
    constructor
    · intro h
      exact (rhs_maximum_zero_iff S).mp (of_decide_eq_true h)
    · intro h
      exact decide_eq_true ((rhs_maximum_zero_iff S).mpr h)

end Maxwell.Cost.MagnitudeMax.Both
