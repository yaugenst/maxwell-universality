import Maxwell.Cost.NormalizeSource.Parse
import Maxwell.Cost.NormalizeCoefficient.FixedWidth
import Maxwell.Cost.SourceCircuit.NormalizedRecord

namespace Maxwell.Cost.NormalizeSource
open Structured RationalAccumulator

structure Ready (s : BitRAMState) : Prop where
  bank : Bank s (fun _ => 0)
  scratch : Scratch s 0
  four : Blank s 4
  coefficient : Blank s 83
  parser : LogEntry.Ready s

def work : Finset ℕ := {0,1,2,3,4,10,12,13,15,16,30,31,32,33,34,35,36,83,85}

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ work → t.tapes i = s.tapes i

def roundedNumerator (scaleNum scaleDen precision : ℕ) (q : ℚ) : ℤ :=
  (Logical.Rounding.nearest precision (q / ((scaleNum : ℚ)/scaleDen))).numerator

def record (scaleNum scaleDen precision row column : ℕ) (q : ℚ) : List Bool :=
  let z := roundedNumerator scaleNum scaleDen precision q
  SourceCircuit.normalizedRecord row column (decide (z < 0)) (Logical.Horner.encode precision z.natAbs)

def entryCode : Code := .seq readEntry
  (.seq NormalizeCoefficient.fixedWidthCode SourceCircuit.normalizedRecordCode)

/-- Read an actual sparse record, normalize and round its coefficient,
then emit exactly the fixed-width signed Horner record. All working words
are reclaimed before the next record. -/
theorem entry_executes (row column : ℕ) (q : ℚ)
    (scaleNum scaleDen precision B : ℕ) (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hrow : row.bits.length ≤ B) (hcolumn : column.bits.length ≤ B)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 →
      (NormalizeCoefficient.values (Codec.RationalPair.canonical q) scaleNum scaleDen precision i).bits.length ≤ B)
    (hsmall : (roundedNumerator scaleNum scaleDen precision q).natAbs < 2^precision)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length) (hready : Ready s.val)
    (hscaleN : Word s.val 80 scaleNum) (hscaleD : Word s.val 81 scaleDen)
    (hpower : Word s.val 82 (2^precision)) (harchive : s.val.tapes 85 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ 130000*(B+2)^2 ∧
      Executes (preceding ++ (ParseEntry.encode row column q ++ suffix)) tape entryCode cost s t ∧
      t.val.inputHead = s.val.inputHead+(ParseEntry.encode row column q).length ∧
      t.val.tapes 85 = BitTape.atEnd (archive ++ record scaleNum scaleDen precision row column q) ∧
      Ready t.val ∧ Frame s.val t.val := by
  let input := preceding ++ (ParseEntry.encode row column q ++ suffix)
  obtain ⟨a, ea, hahead, ha10, ha15, ha16, ha12, ha13, hasign, haf⟩ :=
    readEntry_executes row column q preceding suffix tape s hhead hready.parser
  have akeep (i : ℕ) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h15 : i ≠ 15) (h16 : i ≠ 16) : a.val.tapes i = s.val.tapes i :=
    haf.2.2.2.2.1 i h10 h12 h13 h15 h16
  have abank : Bank a.val (fun _ => 0) := by
    intro i hi hj
    exact word_of_eq (akeep i (by omega) (by omega) (by omega) (by omega) (by omega)) (hready.bank i hi hj)
  have ascratch : Scratch a.val 0 :=
    ⟨blank_of_eq (akeep 0 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.scratch.1,
      word_of_eq (akeep 1 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.scratch.2.1,
      blank_of_eq (akeep 2 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.scratch.2.2.1,
      blank_of_eq (akeep 3 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.scratch.2.2.2⟩
  obtain ⟨ncost, b, hncost, eb, hbout, hbbank, hbscratch, hb4, hb12, hb13, hbf⟩ :=
    NormalizeCoefficient.fixed_width input tape (Codec.RationalPair.canonical q)
      scaleNum scaleDen precision B hscaleNum hscaleDen hbits
      (by simpa [roundedNumerator, Codec.RationalPair.canonical_value] using hsmall)
      a abank ascratch
      (blank_of_eq (akeep 4 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.four)
      (blank_of_eq (akeep 83 (by decide) (by decide) (by decide) (by decide) (by decide)) hready.coefficient)
      ha12 ha13 hasign
      (word_of_eq (akeep 80 (by decide) (by decide) (by decide) (by decide) (by decide)) hscaleN)
      (word_of_eq (akeep 81 (by decide) (by decide) (by decide) (by decide) (by decide)) hscaleD)
      (word_of_eq (akeep 82 (by decide) (by decide) (by decide) (by decide) (by decide)) hpower)
  let z := roundedNumerator scaleNum scaleDen precision q
  have hbout' : NormalizeCoefficient.FixedOutput b.val precision z := by
    simpa [z, roundedNumerator, Codec.RationalPair.canonical_value] using hbout
  obtain ⟨origin, hb83, hbsign⟩ := hbout'
  have bkeep (i : ℕ) (hi : 5 ≤ i) (h12 : i ≠ 12) (h13 : i ≠ 13)
      (h83 : i ≠ 83) (hbank : i < 30 ∨ 36 < i) : b.val.tapes i = a.val.tapes i :=
    hbf.2.2.2.2.2.1 i hi h12 h13 h83 hbank
  obtain ⟨t, et, ht85, ht15, ht16, ht83, htmemory, htf, tkeep⟩ :=
    SourceCircuit.normalizedRecord_executes input tape row column (decide (z < 0))
      (Logical.Horner.encode precision z.natAbs) archive origin b
      ((bkeep 15 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans ha15)
      ((bkeep 16 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans ha16)
      hb83 hbsign
      ((bkeep 85 (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))).trans
        ((akeep 85 (by decide) (by decide) (by decide) (by decide) (by decide)).trans harchive))
  have hlen : (Logical.Horner.encode precision z.natAbs).length = precision := Logical.Horner.encode_length _ _
  refine ⟨_, t, ?_, ea.seq (eb.seq et), ?_, ht85, ?_, ?_⟩
  · have hn := hbits 30 (by decide) (by decide)
    have hd := hbits 31 (by decide) (by decide)
    have hp := hbits 34 (by decide) (by decide)
    simp [NormalizeCoefficient.values, Codec.RationalPair.canonical] at hn hd
    simp [NormalizeCoefficient.values, PowerOfTwo.power_bits] at hp
    rw [hlen]
    nlinarith
  · exact htf.inputHead.trans (hbf.2.1.trans hahead)
  · refine ⟨?_, ?_, blank_of_eq (tkeep 4 (by decide)) hb4,
      ⟨origin+(Logical.Horner.encode precision z.natAbs).length, ht83⟩, ?_⟩
    · intro i hi hj
      exact word_of_eq (tkeep i (by simp [SourceCircuit.recordWork]; omega)) (hbbank i hi hj)
    · exact ⟨blank_of_eq (tkeep 0 (by decide)) hbscratch.1,
        word_of_eq (tkeep 1 (by decide)) hbscratch.2.1,
        blank_of_eq (tkeep 2 (by decide)) hbscratch.2.2.1,
        blank_of_eq (tkeep 3 (by decide)) hbscratch.2.2.2⟩
    · exact ⟨(tkeep 10 (by decide)).trans
          ((bkeep 10 (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))).trans ha10),
        ht15, ht16, (tkeep 12 (by decide)).trans hb12, (tkeep 13 (by decide)).trans hb13⟩
  · refine ⟨htmemory.trans (hbf.2.2.1.trans haf.2.1),
      htf.randomCursor.trans (hbf.2.2.2.1.trans haf.2.2.1),
      htf.output.trans (hbf.2.2.2.2.1.trans haf.2.2.2.1), ?_⟩
    intro i hi
    simp only [work, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact (tkeep i (by simp [SourceCircuit.recordWork]; omega)).trans
      ((bkeep i (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (akeep i (by omega) (by omega) (by omega) (by omega) (by omega)))

end Maxwell.Cost.NormalizeSource
