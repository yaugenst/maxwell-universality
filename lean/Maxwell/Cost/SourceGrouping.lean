import Maxwell.Cost.SourceGrouping.Parse
import Maxwell.Cost.ParseSource

/-! An actual finite sparse-source grouping pass. The retained canonical
record stream is accompanied by one Boolean row-boundary marker per entry.
Dimension and the complete right-hand side remain on their original tapes.
No dense matrix scan or host continuation appears in the machine. -/

namespace Maxwell.Cost.SourceGrouping

set_option maxRecDepth 8192

def program : BitRAM := ⟨
  (ParseNat.programOn 19).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10] ++
  Parse.program.code.map (BitRAMInstruction.relocate 20 433) ++
  ParseRats.program.code.map (BitRAMInstruction.relocate 433 596) ++ [.halt]⟩

theorem dimension_contains : program.Contains (ParseNat.programOn 19) 0 19 := by decide

theorem entries_contains : program.Contains Parse.program 20 433 := by
  intro i
  exact BitRAM.link_lookup
    ((ParseNat.programOn 19).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10])
    Parse.program 433
    (ParseRats.program.code.map (BitRAMInstruction.relocate 433 596) ++ [.halt]) i.val i.isLt

theorem rhs_contains : program.Contains ParseRats.program 433 596 := by
  intro i
  exact BitRAM.link_lookup
    ((ParseNat.programOn 19).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10] ++
      Parse.program.code.map (BitRAMInstruction.relocate 20 433))
    ParseRats.program 596 [.halt] i.val i.isLt

theorem halt_instruction : program.code[596]? = some .halt := by
  have hn : (ParseNat.programOn 19).code.length = 19 := rfl
  have he : Parse.program.code.length = 413 := rfl
  have hr : ParseRats.program.code.length = 163 := rfl
  simp [program, hn, he, hr]

def recordPrice (R : Codec.SourceRecord) : ℕ :=
  17 * R.dimension.bits.length + 11 + Parse.price [] R.entries + ParseRats.price R.rhs

theorem reset_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input tape) 1 {s with pc := 19}
      ((ParseSource.entriesStart s).relocate 20) := by
  apply executeInstructions_sound (instructions := 1)
  have h19 : program.code[19]? = some (.tapeRight 10) := by decide
  simp [executeInstructions, BitRAM.next, h19, BitRAMState.setTape, BitRAMState.relocate,
    ParseSource.entriesStart, hcount, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

/-- Complete operational source pass, starting from the ordinary blank
machine state. Every finite record field is retained exactly. -/
theorem steps_record (R : Codec.SourceRecord) (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ (cost : ℕ) (final : BitRAMState), cost ≤ recordPrice R ∧
      PricedSteps (program.next (ParseSource.recordWire R ++ suffix) tape)
        cost BitRAMState.initial final ∧ final.pc = 596 ∧
      final.inputHead = (ParseSource.recordWire R).length ∧
      final.tapes 19 = BitTape.atEnd R.dimension.bits ∧
      final.tapes 18 = BitTape.atEnd (LogEntries.records R.entries) ∧
      final.tapes 20 = BitTape.atEnd (LogRats.records R.rhs) ∧
      final.tapes 22 = BitTape.atEnd (lastWord [] R.entries) ∧
      final.tapes 24 = BitTape.atEnd (markers [] false R.entries) ∧
      final.randomCursor = 0 ∧ final.output = [] ∧ LogEntry.Ready final := by
  let input := ParseSource.recordWire R ++ suffix
  obtain ⟨d, hd, hdpc, hdhead, hdcount, hdim, hdf⟩ :=
    ParseNat.parse_on_steps 19 (by decide) R.dimension []
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix))
      tape BitRAMState.initial rfl rfl rfl rfl
  have hdi : [] ++ (Codec.nat R.dimension ++
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix))) = input := by
    simp [input, ParseSource.recordWire, List.append_assoc]
  rw [hdi] at hd
  have hdp := dimension_contains.call input tape hd (by
    simp [ParseNat.programOn, BitRAM.renameTapes, ParseNat.program, hdpc, BitRAMInstruction.renameTapes])
  simp only [BitRAMState.relocate_zero] at hdp
  have hestart (i : ℕ) (h10 : i ≠ 10) (h19 : i ≠ 19) :
      (ParseSource.entriesStart d).tapes i = BitTape.blank := by
    simpa [ParseSource.entriesStart, h10, BitRAMState.initial] using hdf.2.2.2.2.1 i h10 h19
  have hehead : (ParseSource.entriesStart d).inputHead = (Codec.nat R.dimension).length := by
    simpa [ParseSource.entriesStart, BitRAMState.initial] using hdhead
  have heready : LogEntry.Ready (ParseSource.entriesStart d) := by
    refine ⟨?_, hestart 15 (by decide) (by decide), hestart 16 (by decide) (by decide),
      hestart 12 (by decide) (by decide), hestart 13 (by decide) (by decide)⟩
    simp [ParseSource.entriesStart]
  have heseen : (ParseSource.entriesStart d).registers 33 = false := by
    simpa [ParseSource.entriesStart, BitRAMState.initial] using
      hdf.2.2.2.2.2 33 (by decide) (by decide) (by decide)
  obtain ⟨c, e, hc, he, hepc, hehead', helog, heprevious, hemarkers, _, heready', hef⟩ :=
    Parse.steps R.entries [] false (Codec.nat R.dimension)
      (Codec.list Codec.rat R.rhs ++ suffix) [] [] tape (ParseSource.entriesStart d) rfl hehead heready
      (hestart 14 (by decide) (by decide))
      (by simpa [BitTape.atEnd_nil] using hestart 18 (by decide) (by decide))
      (by simpa [BitTape.atEnd_nil] using hestart 22 (by decide) (by decide))
      (by simpa [BitTape.atEnd_nil] using hestart 24 (by decide) (by decide)) heseen
  have hei : Codec.nat R.dimension ++
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix)) = input := by
    simp [input, ParseSource.recordWire, List.append_assoc]
  rw [hei] at he
  have hep := entries_contains.call input tape he (by simpa [hepc] using Parse.halt_instruction)
  have heother (i : ℕ) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h14 : i ≠ 14) (h15 : i ≠ 15) (h16 : i ≠ 16) (h18 : i ≠ 18)
      (h19 : i ≠ 19) (h22 : i ≠ 22) (h24 : i ≠ 24) : e.tapes i = BitTape.blank :=
    (hef.2.2.2.2 i h10 h12 h13 h14 h15 h16 h18 h22 h24).trans (hestart i h10 h19)
  have hrhead : e.inputHead =
      (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries).length := by
    simpa [hehead] using hehead'
  obtain ⟨r, hr, hrpc, hrhead', hrlog, hrready, hrf⟩ :=
    ParseRats.steps R.rhs (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries)
      suffix [] tape {e with pc := 0} rfl hrhead
      ⟨heready'.1, heready'.2.2.2.1, heready'.2.2.2.2⟩
      (heother 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
      (by simpa [BitTape.atEnd_nil] using (heother 20 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)))
  have hri : (Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries) ++
      (Codec.list Codec.rat R.rhs ++ suffix) = input := by
    simp [input, ParseSource.recordWire, List.append_assoc]
  rw [hri] at hr
  have hrp := rhs_contains.call input tape hr (by simpa [hrpc] using ParseRats.halt_instruction)
  have hedim : e.tapes 19 = BitTape.atEnd R.dimension.bits := by
    have hh := hef.2.2.2.2 19 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    simpa [ParseSource.entriesStart, hdim] using hh
  refine ⟨17 * R.dimension.bits.length + 11 + c + ParseRats.price R.rhs,
    {r with pc := 596}, by dsimp [recordPrice]; omega, ?_, rfl, ?_,
    (hrf.2.2.2.2 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hedim,
    ?_, by simpa using hrlog, ?_, ?_, ?_, ?_, ?_⟩
  · change PricedSteps (program.next input tape) _ BitRAMState.initial _
    convert ((hdp.trans (reset_block input tape d hdcount)).trans hep).trans hrp using 1
    omega
  · dsimp only at hrhead'
    simpa [ParseSource.recordWire, hrhead, Nat.cast_add, add_assoc] using hrhead'
  · simpa using (hrf.2.2.2.2 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans helog
  · exact (hrf.2.2.2.2 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans heprevious
  · simpa using (hrf.2.2.2.2 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hemarkers
  · exact hrf.2.2.1.trans (hef.2.2.1.trans hdf.2.2.1)
  · exact hrf.2.2.2.1.trans (hef.2.2.2.1.trans hdf.2.2.2.1)
  · exact ⟨hrready.1,
      (hrf.2.2.2.2 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans heready'.2.1,
      (hrf.2.2.2.2 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans heready'.2.2.1,
      hrready.2.1, hrready.2.2⟩

/-- Encoded-bit cost with only the three actually parsed count widths. -/
theorem recordPrice_le (R : Codec.SourceRecord) :
    recordPrice R ≤ 100 * ((ParseSource.recordWire R).length + 1) *
      (R.dimension.bits.length + R.entries.length.bits.length + R.rhs.length.bits.length + 1) := by
  have he := Parse.price_le R.entries
  have hr := ParseRats.price_le R.rhs
  have hl := ParseSource.recordWire_length R
  have hlenE := LogEntries.records_length R.entries
  have hlenR := LogRats.records_length R.rhs
  let B := (ParseSource.recordWire R).length
  let K := R.dimension.bits.length + R.entries.length.bits.length + R.rhs.length.bits.length + 1
  have hn : R.entries.length + 1 ≤ B + 1 := by dsimp [B]; omega
  have hm : R.rhs.length + 1 ≤ B + 1 := by dsimp [B]; omega
  have hkE : 13 * R.entries.length.bits.length + 13 ≤ 13 * K := by dsimp [K]; omega
  have hkR : 13 * R.rhs.length.bits.length + 13 ≤ 13 * K := by dsimp [K]; omega
  have heCounter : (R.entries.length + 1) * (13 * R.entries.length.bits.length + 13) ≤
      13 * (B + 1) * K := by
    calc
      _ ≤ (B + 1) * (13 * K) := Nat.mul_le_mul hn hkE
      _ = _ := by ring
  have hrCounter : (R.rhs.length + 1) * (13 * R.rhs.length.bits.length + 13) ≤
      13 * (B + 1) * K := by
    calc
      _ ≤ (B + 1) * (13 * K) := Nat.mul_le_mul hm hkR
      _ = _ := by ring
  have hlinear : 17 * R.dimension.bits.length + 21 * R.entries.length.bits.length +
      21 * R.rhs.length.bits.length + 43 + 53 * (LogEntries.records R.entries).length +
      29 * (LogRats.records R.rhs).length ≤ 53 * (B + 1) := by dsimp [B]; omega
  have hk : 1 ≤ K := by dsimp [K]; omega
  have hbase : B + 1 ≤ (B + 1) * K := by nlinarith
  change recordPrice R ≤ 100 * (B + 1) * K
  dsimp only [recordPrice]
  nlinarith

def price (S : Source.SparseSystem) : ℕ := recordPrice (Codec.sourceRecord S)

theorem price_le (S : Source.SparseSystem) :
    price S ≤ 100 * ((Codec.source S).length + 1) *
      (2 * S.n.bits.length + S.nnz.bits.length + 1) := by
  have h := recordPrice_le (Codec.sourceRecord S)
  rw [ParseSource.source_wire] at h
  simpa [price, Codec.sourceRecord, Codec.sourceEntries_length,
    two_mul, add_assoc, add_left_comm, add_comm] using h

/-- A single fixed finite program groups the actual canonical source input.
The fuel cap includes one final halt observation; unused suffix bits are untouched. -/
theorem run (S : Source.SparseSystem) (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ final : BitRAMState,
      (program.run (Codec.source S ++ suffix) tape (price S + 1)).finished = some final ∧
      (program.run (Codec.source S ++ suffix) tape (price S + 1)).instructions ≤ price S ∧
      final.inputHead = (Codec.source S).length ∧
      final.tapes 19 = BitTape.atEnd S.n.bits ∧
      final.tapes 18 = BitTape.atEnd (LogEntries.records (Codec.sourceRecord S).entries) ∧
      final.tapes 20 = BitTape.atEnd (LogRats.records (List.ofFn S.source)) ∧
      final.tapes 24 = BitTape.atEnd (markers [] false (Codec.sourceRecord S).entries) ∧
      final.randomCursor = 0 ∧ final.output = [] ∧ LogEntry.Ready final := by
  obtain ⟨c, final, hc, hs, hp, hh, hd, he, hr, _, hb, hrandom, hout, hready⟩ :=
    steps_record (Codec.sourceRecord S) suffix tape
  rw [ParseSource.source_wire] at hs hh
  have hrun := hs.runPriced_ge (by simp [BitRAM.next, hp, halt_instruction]) (price S + 1) (by
    change c + 1 ≤ recordPrice (Codec.sourceRecord S) + 1
    omega)
  exact ⟨final, hrun.1, hrun.2.trans_le hc, hh, hd, he, hr, hb,
    hrandom, hout, hready⟩

end Maxwell.Cost.SourceGrouping
