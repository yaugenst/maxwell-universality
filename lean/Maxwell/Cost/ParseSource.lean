import Maxwell.Cost.ParseEntries
import Maxwell.Cost.ParseRats

/-! A single finite program parses the canonical sparse source. Dimension
bits remain on tape 19, complete sparse-entry records on tape 18, and all
right-hand-side rational records on tape 20. The machine reads both list
counts from its input; no dense matrix traversal or answer oracle occurs. -/

namespace Maxwell.Cost.ParseSource

def program : BitRAM := ⟨
  (ParseNat.programOn 19).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10] ++
  ParseEntries.program.code.map (BitRAMInstruction.relocate 20 296) ++
  ParseRats.program.code.map (BitRAMInstruction.relocate 296 459) ++ [.halt]⟩

theorem dimension_contains : program.Contains (ParseNat.programOn 19) 0 19 := by decide
set_option maxRecDepth 8192 in
theorem entries_contains : program.Contains ParseEntries.program 20 296 := by decide
set_option maxRecDepth 8192 in
theorem rhs_contains : program.Contains ParseRats.program 296 459 := by decide
theorem halt_instruction : program.code[459]? = some .halt := by decide

def recordWire (R : Codec.SourceRecord) : List Bool :=
  Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries ++ Codec.list Codec.rat R.rhs

def recordPrice (R : Codec.SourceRecord) : ℕ :=
  17 * R.dimension.bits.length + 11 + ParseEntries.price R.entries + ParseRats.price R.rhs

def Scratch (s : BitRAMState) : Prop :=
  LogEntry.Ready s ∧ s.tapes 14 = BitTape.blank ∧ s.tapes 19 = BitTape.blank ∧ s.tapes 21 = BitTape.blank

def scratchTapes : Finset ℕ := {10, 12, 13, 14, 15, 16, 18, 19, 20, 21}

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧ ∀ i, i ∉ scratchTapes → t.tapes i = s.tapes i

def entriesStart (s : BitRAMState) : BitRAMState :=
  {s with pc := 0, tapes := Function.update s.tapes 10 BitTape.blank}

theorem reset_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input tape) 1 {s with pc := 19} ((entriesStart s).relocate 20) := by
  apply executeInstructions_sound (instructions := 1)
  have h19 : program.code[19]? = some (.tapeRight 10) := by decide
  simp [executeInstructions, BitRAM.next, h19, BitRAMState.setTape, BitRAMState.relocate,
    entriesStart, hcount, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

theorem steps_record (R : Codec.SourceRecord) (preceding suffix entryArchive rhsArchive : List Bool)
    (tape : ℕ → Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hscratch : Scratch initial)
    (hentries : initial.tapes 18 = BitTape.atEnd entryArchive)
    (hrhs : initial.tapes 20 = BitTape.atEnd rhsArchive) :
    ∃ final : BitRAMState,
      PricedSteps (program.next (preceding ++ (recordWire R ++ suffix)) tape)
        (recordPrice R) initial final ∧
      final.pc = 459 ∧ final.inputHead = initial.inputHead + (recordWire R).length ∧
      final.tapes 19 = BitTape.atEnd R.dimension.bits ∧
      final.tapes 18 = BitTape.atEnd (entryArchive ++ LogEntries.records R.entries) ∧
      final.tapes 20 = BitTape.atEnd (rhsArchive ++ LogRats.records R.rhs) ∧
      LogEntry.Ready final ∧ Frame initial final := by
  let input := preceding ++ (recordWire R ++ suffix)
  obtain ⟨d, hd, hdpc, hdhead, hdcount, hdim, hdframe⟩ :=
    ParseNat.parse_on_steps 19 (by decide) R.dimension preceding
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix))
      tape initial hpc hhead hscratch.1.1 hscratch.2.2.1
  have hdi : preceding ++ (Codec.nat R.dimension ++
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix))) = input := by
    simp [input, recordWire, List.append_assoc]
  rw [hdi] at hd
  have hdp := dimension_contains.call input tape hd (by
    simp [ParseNat.programOn, BitRAM.renameTapes, ParseNat.program, hdpc,
      BitRAMInstruction.renameTapes])
  simp only [BitRAMState.relocate_zero] at hdp
  have hestart (i : ℕ) (h10 : i ≠ 10) (h19 : i ≠ 19) :
      (entriesStart d).tapes i = initial.tapes i := by
    simpa [entriesStart, h10] using hdframe.2.2.2.2.1 i h10 h19
  have hehead : (entriesStart d).inputHead = (preceding ++ Codec.nat R.dimension).length := by
    simpa [entriesStart, hhead] using hdhead
  have heready : LogEntry.Ready (entriesStart d) := by
    refine ⟨?_, (hestart 15 (by decide) (by decide)).trans hscratch.1.2.1,
      (hestart 16 (by decide) (by decide)).trans hscratch.1.2.2.1,
      (hestart 12 (by decide) (by decide)).trans hscratch.1.2.2.2.1,
      (hestart 13 (by decide) (by decide)).trans hscratch.1.2.2.2.2⟩
    simp [entriesStart]
  obtain ⟨e, he, hepc, hehead', helog, heready', heframe⟩ :=
    ParseEntries.steps R.entries (preceding ++ Codec.nat R.dimension)
      (Codec.list Codec.rat R.rhs ++ suffix) entryArchive tape (entriesStart d) rfl hehead heready
      ((hestart 14 (by decide) (by decide)).trans hscratch.2.1)
      ((hestart 18 (by decide) (by decide)).trans hentries)
  have hei : (preceding ++ Codec.nat R.dimension) ++
      (Codec.list LogEntries.encodeEntry R.entries ++ (Codec.list Codec.rat R.rhs ++ suffix)) = input := by
    simp [input, recordWire, List.append_assoc]
  rw [hei] at he
  have hep := entries_contains.call input tape he (by simpa [hepc] using ParseEntries.halt_instruction)
  have heother (i : ℕ) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h14 : i ≠ 14) (h15 : i ≠ 15) (h16 : i ≠ 16) (h18 : i ≠ 18) (h19 : i ≠ 19) :
      e.tapes i = initial.tapes i :=
    (heframe.2.2.2.2 i h10 h12 h13 h14 h15 h16 h18).trans (hestart i h10 h19)
  have hrhead : e.inputHead =
      (preceding ++ Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries).length := by
    simp only [entriesStart] at hehead'
    simp only [List.length_append, Nat.cast_add]
    simp only [hhead] at hdhead
    omega
  obtain ⟨r, hr, hrpc, hrhead', hrlog, hrready, hrframe⟩ :=
    ParseRats.steps R.rhs
      (preceding ++ Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries)
      suffix rhsArchive tape {e with pc := 0} rfl hrhead
      ⟨heready'.1, heready'.2.2.2.1, heready'.2.2.2.2⟩
      ((heother 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hscratch.2.2.2)
      ((heother 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hrhs)
  have hri : (preceding ++ Codec.nat R.dimension ++ Codec.list LogEntries.encodeEntry R.entries) ++
      (Codec.list Codec.rat R.rhs ++ suffix) = input := by
    simp [input, recordWire, List.append_assoc]
  rw [hri] at hr
  have hrp := rhs_contains.call input tape hr (by simpa [hrpc] using ParseRats.halt_instruction)
  have hedim : e.tapes 19 = BitTape.atEnd R.dimension.bits := by
    have hh := heframe.2.2.2.2 19 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    simpa [entriesStart, hdim] using hh
  refine ⟨{r with pc := 459}, ?_, rfl, ?_,
    (hrframe.2.2.2.2 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hedim,
    (hrframe.2.2.2.2 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans helog,
    hrlog, ?_, ?_⟩
  · change PricedSteps (program.next input tape) _ initial _
    convert ((hdp.trans (reset_block input tape d hdcount)).trans hep).trans hrp using 1
    dsimp [recordPrice]
    omega
  · simp only [entriesStart] at hehead'
    dsimp only at hrhead'
    simp only [recordWire, List.length_append]
    omega
  · exact ⟨hrready.1,
      (hrframe.2.2.2.2 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans heready'.2.1,
      (hrframe.2.2.2.2 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans heready'.2.2.1,
      hrready.2.1, hrready.2.2⟩
  · refine ⟨hrframe.1.trans (heframe.1.trans hdframe.1),
      hrframe.2.1.trans (heframe.2.1.trans hdframe.2.1),
      hrframe.2.2.1.trans (heframe.2.2.1.trans hdframe.2.2.1),
      hrframe.2.2.2.1.trans (heframe.2.2.2.1.trans hdframe.2.2.2.1), ?_⟩
    intro i hi
    simp only [scratchTapes, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rcases hi with ⟨h10, h12, h13, h14, h15, h16, h18, h19, h20, h21⟩
    exact (hrframe.2.2.2.2 i h10 h12 h13 h21 h20).trans
      (heother i h10 h12 h13 h14 h15 h16 h18 h19)

theorem source_wire (S : Source.SparseSystem) : recordWire (Codec.sourceRecord S) = Codec.source S := by
  rw [recordWire, ParseEntries.source_entry_list]
  rfl

def price (S : Source.SparseSystem) : ℕ := recordPrice (Codec.sourceRecord S)

theorem steps (S : Source.SparseSystem) (preceding suffix entryArchive rhsArchive : List Bool)
    (tape : ℕ → Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hscratch : Scratch initial)
    (hentries : initial.tapes 18 = BitTape.atEnd entryArchive)
    (hrhs : initial.tapes 20 = BitTape.atEnd rhsArchive) :
    ∃ final : BitRAMState,
      PricedSteps (program.next (preceding ++ (Codec.source S ++ suffix)) tape)
        (price S) initial final ∧
      final.pc = 459 ∧ final.inputHead = initial.inputHead + (Codec.source S).length ∧
      final.tapes 19 = BitTape.atEnd S.n.bits ∧
      final.tapes 18 = BitTape.atEnd (entryArchive ++ LogEntries.records (Codec.sourceRecord S).entries) ∧
      final.tapes 20 = BitTape.atEnd (rhsArchive ++ LogRats.records (List.ofFn S.source)) ∧
      LogEntry.Ready final ∧ Frame initial final := by
  have h := steps_record (Codec.sourceRecord S) preceding suffix entryArchive rhsArchive tape initial
    hpc hhead hscratch hentries hrhs
  rw [source_wire] at h
  simpa only [Codec.sourceRecord, price] using h

theorem run (S : Source.SparseSystem) (suffix : List Bool) (tape : ℕ → Bool) :
    ∃ final : BitRAMState,
      (program.run (Codec.source S ++ suffix) tape (price S + 1)).finished = some final ∧
      (program.run (Codec.source S ++ suffix) tape (price S + 1)).instructions = price S ∧
      final.inputHead = (Codec.source S).length ∧
      final.tapes 19 = BitTape.atEnd S.n.bits ∧
      final.tapes 18 = BitTape.atEnd (LogEntries.records (Codec.sourceRecord S).entries) ∧
      final.tapes 20 = BitTape.atEnd (LogRats.records (List.ofFn S.source)) ∧
      LogEntry.Ready final ∧ Frame BitRAMState.initial final := by
  obtain ⟨final, hf, hfpc, hh, hd, he, hr, hready, hframe⟩ :=
    steps S [] suffix [] [] tape BitRAMState.initial rfl rfl
      (by simp [Scratch, LogEntry.Ready, BitRAMState.initial])
      (by simp [BitRAMState.initial, BitTape.atEnd_nil])
      (by simp [BitRAMState.initial, BitTape.atEnd_nil])
  obtain ⟨hfinished, hcost⟩ := hf.runPriced (by simp [BitRAM.next, hfpc, halt_instruction])
  refine ⟨final, hfinished, hcost, ?_, hd, ?_, ?_, hready, hframe⟩
  · simpa [BitRAMState.initial] using hh
  · simpa using he
  · simpa using hr

theorem recordWire_length (R : Codec.SourceRecord) :
    (recordWire R).length =
      2 * (R.dimension.bits.length + R.entries.length.bits.length + R.rhs.length.bits.length) +
      (LogEntries.records R.entries).length + (LogRats.records R.rhs).length + 3 := by
  simp [recordWire, Codec.list, Codec.nat, LogEntries.records, LogRats.records]
  omega

theorem recordPrice_le (R : Codec.SourceRecord) :
    recordPrice R ≤ 64 * ((recordWire R).length + 1) *
      (R.dimension.bits.length + R.entries.length.bits.length + R.rhs.length.bits.length + 1) := by
  have he := ParseEntries.price_le R.entries
  have hr := ParseRats.price_le R.rhs
  have hl := recordWire_length R
  have hlenE := LogEntries.records_length R.entries
  have hlenR := LogRats.records_length R.rhs
  let B := (recordWire R).length
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
      21 * R.rhs.length.bits.length + 43 + 34 * (LogEntries.records R.entries).length +
      29 * (LogRats.records R.rhs).length ≤ 34 * (B + 1) := by dsimp [B]; omega
  have hk : 1 ≤ K := by dsimp [K]; omega
  have hbase : B + 1 ≤ (B + 1) * K := by nlinarith
  change recordPrice R ≤ 64 * (B + 1) * K
  dsimp only [recordPrice]
  nlinarith

/-- A complete bound in encoded input bits and the two actual count widths. -/
theorem price_le (S : Source.SparseSystem) :
    price S ≤ 64 * ((Codec.source S).length + 1) *
      (2 * S.n.bits.length + S.nnz.bits.length + 1) := by
  have h := recordPrice_le (Codec.sourceRecord S)
  rw [source_wire] at h
  simpa [price, Codec.sourceRecord, Codec.sourceEntries_length,
    two_mul, add_assoc, add_left_comm, add_comm] using h

theorem entry_records_parse (S : Source.SparseSystem) (suffix : List Bool) :
    Codec.readMany Codec.readSourceEntry S.nnz
      (LogEntries.records (Codec.sourceRecord S).entries ++ suffix) =
        some ((Codec.sourceRecord S).entries, suffix) := by
  have h := Codec.readMany_append LogEntries.encodeEntry Codec.readSourceEntry
    (fun p tail => ParseEntry.wire_roundtrip p.1 p.2.1 p.2.2 tail)
    (Codec.sourceRecord S).entries suffix
  simpa [LogEntries.records, Codec.sourceRecord, Codec.sourceEntries_length] using h

theorem rhs_records_parse (S : Source.SparseSystem) (suffix : List Bool) :
    Codec.readMany Codec.readRat S.n (LogRats.records (List.ofFn S.source) ++ suffix) =
      some (List.ofFn S.source, suffix) := by
  simpa [LogRats.records] using Codec.readMany_append Codec.rat Codec.readRat Codec.readRat_append
    (List.ofFn S.source) suffix

end Maxwell.Cost.ParseSource
