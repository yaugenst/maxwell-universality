import Maxwell.Cost.NormalizeSource.Loop
import Maxwell.Cost.DecoderParser.ReadFields

namespace Maxwell.Cost.NormalizeSource
open Structured RationalAccumulator

def matrixPassCode : Code := .seq (DecoderParser.readNatural 75)
  (.seq (DecoderParser.readNatural 74) loopCode)

def matrixPassPrice (dimension : ℕ) (entries : List Entry) (B : ℕ) : ℕ :=
  21*dimension.bits.length+16+21*entries.length.bits.length+16+
    loopPrice entries.length.bits entries B

private theorem ready_read {s t : BitRAMState} {target : ℕ}
    (htarget : target = 74 ∨ target = 75) (hf : DecoderParser.Frame {target} s t)
    (hr : Ready s) : Ready t := by
  have ht (i : ℕ) (hi : i ≠ target) : t.tapes i = s.tapes i := hf.tapes i (by simpa using hi)
  refine ⟨?_, ?_, blank_of_eq (ht 4 (by omega)) hr.four,
    blank_of_eq (ht 83 (by omega)) hr.coefficient, ?_⟩
  · intro i hi hj
    exact word_of_eq (ht i (by omega)) (hr.bank i hi hj)
  · exact ⟨blank_of_eq (ht 0 (by omega)) hr.scratch.1,
      word_of_eq (ht 1 (by omega)) hr.scratch.2.1,
      blank_of_eq (ht 2 (by omega)) hr.scratch.2.2.1,
      blank_of_eq (ht 3 (by omega)) hr.scratch.2.2.2⟩
  · exact ⟨(ht 10 (by omega)).trans hr.parser.1, (ht 15 (by omega)).trans hr.parser.2.1,
      (ht 16 (by omega)).trans hr.parser.2.2.1, (ht 12 (by omega)).trans hr.parser.2.2.2.1,
      (ht 13 (by omega)).trans hr.parser.2.2.2.2⟩

/-- The second source pass reads its dimensions and entry count from the
canonical input, then executes the finite sparse normalization loop. -/
theorem matrixPass_executes (dimension : ℕ) (entries : List Entry)
    (scaleNum scaleDen precision B : ℕ) (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hwidth : ∀ p ∈ entries, Width scaleNum scaleDen precision B p)
    (suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = 0) (hready : Ready s.val)
    (h74 : s.val.tapes 74 = BitTape.blank) (h75 : s.val.tapes 75 = BitTape.blank)
    (hscaleN : Word s.val 80 scaleNum) (hscaleD : Word s.val 81 scaleDen)
    (hpower : Word s.val 82 (2^precision)) (harchive : s.val.tapes 85 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ matrixPassPrice dimension entries B ∧
      Executes (Codec.nat dimension ++ (Codec.list LogEntries.encodeEntry entries ++ suffix))
        tape matrixPassCode cost s t ∧
      t.val.inputHead = (Codec.nat dimension ++ Codec.list LogEntries.encodeEntry entries).length ∧
      t.val.tapes 85 = BitTape.atEnd (archive ++ records scaleNum scaleDen precision entries) ∧
      Ready t.val ∧ t.val.memory = s.val.memory ∧ t.val.randomCursor = s.val.randomCursor ∧
      t.val.output = s.val.output ∧
      (∀ i, i ≠ 74 → i ≠ 75 → i ∉ work → t.val.tapes i = s.val.tapes i) := by
  let input := Codec.nat dimension ++ (Codec.list LogEntries.encodeEntry entries ++ suffix)
  obtain ⟨a, ea, hahead, _, ha10, haf⟩ := DecoderParser.readNatural_steps 75 (by decide)
    dimension [] (Codec.list LogEntries.encodeEntry entries ++ suffix) tape s hhead hready.parser.1 h75
  have hahead' : a.val.inputHead = (Codec.nat dimension).length := by simpa [hhead] using hahead
  obtain ⟨b, eb, hbhead, hb74, _, hbf⟩ := DecoderParser.readNatural_steps 74 (by decide)
    entries.length (Codec.nat dimension) (LogEntries.records entries ++ suffix) tape a hahead' ha10
    ((haf.tapes 74 (by decide)).trans h74)
  have hi : Codec.nat dimension ++ (Codec.nat entries.length ++ (LogEntries.records entries ++ suffix)) = input := by
    simp [input, Codec.list, LogEntries.records, List.append_assoc]
  rw [hi] at eb
  have bkeep (i : ℕ) (h74 : i ≠ 74) (h75 : i ≠ 75) : b.val.tapes i = s.val.tapes i :=
    (hbf.tapes i (by simpa using h74)).trans (haf.tapes i (by simpa using h75))
  have bready := ready_read (Or.inl rfl) hbf (ready_read (Or.inr rfl) haf hready)
  have hbhead' : b.val.inputHead = (Codec.nat dimension ++ Codec.nat entries.length).length := by
    simp only [List.length_append, Nat.cast_add]
    omega
  obtain ⟨c, t, hc, et, hthead, htlog, htready, htf⟩ := loop_executes entries
    scaleNum scaleDen precision B hscaleNum hscaleDen hwidth entries.length.bits
    (Codec.nat dimension ++ Codec.nat entries.length) suffix archive tape b hbhead'
    (address_bits _) hb74 bready
    (word_of_eq (bkeep 80 (by decide) (by decide)) hscaleN)
    (word_of_eq (bkeep 81 (by decide) (by decide)) hscaleD)
    (word_of_eq (bkeep 82 (by decide) (by decide)) hpower)
    ((bkeep 85 (by decide) (by decide)).trans harchive)
  have hi' : (Codec.nat dimension ++ Codec.nat entries.length) ++
      (LogEntries.records entries ++ suffix) = input := by
    simp [input, Codec.list, LogEntries.records, List.append_assoc]
  rw [hi'] at et
  refine ⟨_, t, by dsimp [matrixPassPrice]; omega, ea.seq (eb.seq et), ?_, htlog, htready,
    htf.memory.trans (hbf.memory.trans haf.memory),
    htf.randomCursor.trans (hbf.randomCursor.trans haf.randomCursor),
    htf.output.trans (hbf.output.trans haf.output), ?_⟩
  · simp only [Codec.list, List.length_append, Nat.cast_add]
    simp only [LogEntries.records] at hthead
    omega
  · intro i h74 h75 hi
    exact (htf.tapes i h74 hi).trans (bkeep i h74 h75)

end Maxwell.Cost.NormalizeSource
