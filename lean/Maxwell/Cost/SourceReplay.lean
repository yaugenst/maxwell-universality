import Maxwell.Cost.SourceReplay.Archive
import Maxwell.Cost.SourceReplay.Header
import Maxwell.Cost.ParseSource
import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.SourceReplay
open Structured RationalAccumulator

def code : Code := .seq (.call (Archive.program 18))
  (.seq (.call (Archive.program 20))
    (.seq (Header.code 19) (.seq (Header.code 19) (Header.code 79))))

def price (R : Codec.SourceRecord) : ℕ :=
  6*((LogEntries.records R.entries).length+(LogRats.records R.rhs).length)+
    22*R.dimension.bits.length+11*R.entries.length.bits.length+45

structure Frame (s t : Store) : Prop where
  address : t.val.address = s.val.address
  memory : t.val.memory = s.val.memory
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ j, j ≠ 18 → j ≠ 20 → t.val.tapes j = s.val.tapes j

/-- Replay begins at the true source wire's first bit. Its cursor displacement
is derived from actual archived records and retained binary headers. -/
theorem executes (R : Codec.SourceRecord) (hrhs : R.rhs.length = R.dimension)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = (ParseSource.recordWire R).length)
    (hdim : Word s.val 19 R.dimension) (hcount : Word s.val 79 R.entries.length)
    (hentries : s.val.tapes 18 = BitTape.atEnd (LogEntries.records R.entries))
    (hrats : s.val.tapes 20 = BitTape.atEnd (LogRats.records R.rhs)) :
    ∃ t : Store, Executes input randomTape code (price R) s t ∧
      t.val.inputHead = 0 ∧
      t.val.tapes 18 = BitTape.ofList (LogEntries.records R.entries) ∧
      t.val.tapes 20 = BitTape.ofList (LogRats.records R.rhs) ∧ Frame s t := by
  obtain ⟨a, ea, hahead, ha18, haf⟩ := Archive.executes 18 input randomTape
    (LogEntries.records R.entries) s (by simpa [BitTape.atEnd, BitTape.shiftedEnd, BitTape.shifted,
      BitTape.ofList] using hentries)
  obtain ⟨b, eb, hbhead, hb20, hbf⟩ := Archive.executes 20 input randomTape
    (LogRats.records R.rhs) a (by simpa [haf.tapes 20 (by decide), BitTape.atEnd,
      BitTape.shiftedEnd, BitTape.shifted, BitTape.ofList] using hrats)
  have hbkeep (i : ℕ) (h18 : i ≠ 18) (h20 : i ≠ 20) : b.val.tapes i = s.val.tapes i :=
    (hbf.tapes i h20).trans (haf.tapes i h18)
  obtain ⟨dimOrigin, hdim⟩ := hdim
  obtain ⟨c, ec, hchead, hcf⟩ := Header.executes 19 R.dimension dimOrigin input randomTape b
    ((hbkeep 19 (by decide) (by decide)).trans hdim)
  obtain ⟨d, ed, hdhead, hdf⟩ := Header.executes 19 R.dimension dimOrigin input randomTape c
    ((congrFun hcf.tapes 19).trans ((hbkeep 19 (by decide) (by decide)).trans hdim))
  obtain ⟨countOrigin, hcount⟩ := hcount
  obtain ⟨t, et, hthead, htf⟩ := Header.executes 79 R.entries.length countOrigin input randomTape d
    ((congrFun hdf.tapes 79).trans ((congrFun hcf.tapes 79).trans
      ((hbkeep 79 (by decide) (by decide)).trans hcount)))
  have htapes : t.val.tapes = b.val.tapes := htf.tapes.trans (hdf.tapes.trans hcf.tapes)
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · convert ea.seq (eb.seq (ec.seq (ed.seq et))) using 1 <;> first | rfl | (dsimp [price]; omega)
  · have hlength : (ParseSource.recordWire R).length =
        2*(Codec.nat R.dimension).length+(Codec.nat R.entries.length).length+
          (LogEntries.records R.entries).length+(LogRats.records R.rhs).length := by
      simp [ParseSource.recordWire, Codec.list, LogEntries.records, LogRats.records, hrhs]
      omega
    rw [hthead, hdhead, hchead, hbhead, hahead, hhead, hlength]
    push_cast
    omega
  · exact (congrFun htapes 18).trans ((hbf.tapes 18 (by decide)).trans ha18)
  · exact (congrFun htapes 20).trans hb20
  · refine ⟨htf.address.trans (hdf.address.trans (hcf.address.trans (hbf.address.trans haf.address))),
      htf.memory.trans (hdf.memory.trans (hcf.memory.trans (hbf.memory.trans haf.memory))),
      htf.randomCursor.trans (hdf.randomCursor.trans (hcf.randomCursor.trans
        (hbf.randomCursor.trans haf.randomCursor))),
      htf.output.trans (hdf.output.trans (hcf.output.trans (hbf.output.trans haf.output))), ?_⟩
    intro j h18 h20
    exact (congrFun htapes j).trans (hbkeep j h18 h20)

/-- Rewinding is linear in bytes already read, with binary header scans
charged explicitly. -/
theorem price_le (R : Codec.SourceRecord) :
    price R ≤ 11*(ParseSource.recordWire R).length+45 := by
  have hnat (n : ℕ) : 2*n.bits.length+1 = (Codec.nat n).length := by
    simp [Codec.nat]
    omega
  have hn := hnat R.dimension
  have hm := hnat R.entries.length
  dsimp [price, ParseSource.recordWire, Codec.list, LogEntries.records, LogRats.records]
  simp only [List.length_append]
  omega

end Maxwell.Cost.SourceReplay
