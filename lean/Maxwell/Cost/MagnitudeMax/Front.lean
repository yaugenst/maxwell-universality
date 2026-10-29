import Maxwell.Cost.MagnitudeMax.Initialize
import Maxwell.Cost.MagnitudeMax.Entries
import Maxwell.Cost.ParseSource

namespace Maxwell.Cost.MagnitudeMax.Front

open Structured RationalAccumulator

def code : Code := .seq initializeCode (.seq (DecoderParser.readNatural 19) Entries.code)

def price (R : Codec.SourceRecord) (B : ℕ) : ℕ :=
  4 + (21 * R.dimension.bits.length + 16) + Entries.price R.entries B

def work : Finset ℕ := {0, 1, 2, 3, 10, 12, 13, 14, 15, 16, 18, 19, 22, 24, 30, 31, 32, 33, 34, 35, 36, 79}

/-- The matrix prefix retains the actual parsed nonzero count on tape 79
before destructive countdown. RHS bits have not yet been consumed. -/
theorem executes (R : Codec.SourceRecord) (B : ℕ) (hB : 1 ≤ B)
    (hwidth : ∀ p ∈ R.entries, SourceLoop.Width B p) (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ cost, ∃ t : Store, cost ≤ price R B ∧
      Executes (ParseSource.recordWire R ++ suffix) tape code cost (Store.ofState BitRAMState.initial) t ∧
      t.val.inputHead = (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries).length ∧
      Bank t.val (bankOf (maximum (SourceLoop.values R.entries))) ∧ Scratch t.val 0 ∧ LogEntry.Ready t.val ∧
      Word t.val 79 R.entries.length ∧
      t.val.tapes 19 = BitTape.ofList R.dimension.bits ∧
      t.val.tapes 18 = BitTape.atEnd (LogEntries.records R.entries) ∧
      t.val.tapes 24 = BitTape.atEnd (SourceGrouping.markers [] false R.entries) ∧
      t.val.randomCursor = 0 ∧ t.val.output = [] ∧
      (∀ i ∉ work, t.val.tapes i = BitTape.blank) := by
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
  obtain ⟨ec, e, hec, he, hehead, heb, her, heparser, helog, _, hemarkers, he79, hef⟩ :=
    Entries.executes R.entries (0, 1) B (Codec.nat R.dimension)
      (Codec.list Codec.rat R.rhs ++ suffix) [] tape d hdnext (hdblank 14 (by decide) (by decide))
      ⟨0, by simpa [BitTape.blank] using hdblank 79 (by decide) (by decide)⟩
      (by decide) (by simp [hB]) hwidth hdb hdr hdparser
      (by simpa [BitTape.atEnd_nil] using hdblank 18 (by decide) (by decide))
      (by simpa [BitTape.atEnd_nil] using hdblank 22 (by decide) (by decide))
      (by simpa [BitTape.atEnd_nil] using hdblank 24 (by decide) (by decide))
  have hei : Codec.nat R.dimension ++
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix)) = input := by
    simp [input, ParseSource.recordWire, List.append_assoc]
  rw [hei] at he
  refine ⟨4 + ((21 * R.dimension.bits.length + 16) + ec), e, by dsimp [price]; omega,
    hs.seq (hd.seq he), by simpa [hdnext] using hehead, heb, her, heparser, he79, ?_,
    by simpa using helog, hemarkers, hef.2.2.1.trans hdf.randomCursor,
    hef.2.2.2.1.trans hdf.output, ?_⟩
  · exact (hef.2.2.2.2 19 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by decide))).trans hdim
  · intro i hi
    simp only [work, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact (hef.2.2.2.2 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hdblank i (by omega) (by omega))

end Maxwell.Cost.MagnitudeMax.Front
