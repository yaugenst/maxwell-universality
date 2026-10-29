import Maxwell.Cost.NormalizeSource.RhsLog
import Maxwell.Cost.DecoderParser.Primitives
import Maxwell.Cost.LogRat

namespace Maxwell.Cost.NormalizeSource.Rhs
open Structured RationalAccumulator

structure Ready (s : BitRAMState) : Prop where
  bank : Bank s (fun _ => 0)
  scratch : Scratch s 0
  four : Blank s 4
  parser : LogRat.Ready s

def work : Finset ℕ := {0,1,2,3,4,10,12,13,30,31,32,33,34,35,36,88}

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ work → t.tapes i = s.tapes i

def numerator (scaleNum scaleDen precision : ℕ) (q : ℚ) : ℤ :=
  (Logical.Rounding.nearest precision (q / ((scaleNum : ℚ)/scaleDen))).numerator

def record (scaleNum scaleDen precision : ℕ) (q : ℚ) : List Bool :=
  Codec.int (numerator scaleNum scaleDen precision q)

def readCode : Code := .seq (.call ParseRat.program) (.call DecoderParser.resetCounter)

theorem reads (q : ℚ) (preceding suffix : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length) (hready : LogRat.Ready s.val) :
    ∃ t : Store, Executes (preceding ++ (Codec.rat q ++ suffix)) tape readCode
      (17*(q.num.natAbs.bits.length+q.den.bits.length)+23) s t ∧
      t.val.inputHead = s.val.inputHead+(Codec.rat q).length ∧
      t.val.tapes 10 = BitTape.blank ∧
      t.val.tapes 12 = BitTape.atEnd q.num.natAbs.bits ∧ t.val.tapes 13 = BitTape.atEnd q.den.bits ∧
      t.val.registers 23 = decide (q.num < 0) ∧ ParseRat.Frame s.val t.val := by
  obtain ⟨u, eu, hup, huh, hu10, hu12, hu13, hus, huf⟩ := ParseRat.parse_rat_steps
    q preceding suffix tape s.val s.property hhead hready.1 hready.2.1 hready.2.2
  have e1 := Executes.call ParseRat.program s u _ eu (by rw [hup]; decide)
  have e2 := DecoderParser.resetCounter_steps
    (preceding ++ (Codec.rat q ++ suffix)) tape (Store.ofState u) hu10
  let t := Store.ofState (DecoderParser.resetCounterState u)
  refine ⟨t, e1.seq e2, huh, ?_, ?_, ?_, hus, ?_⟩
  · simp [t, Store.ofState, DecoderParser.resetCounterState]
  · simpa [t, Store.ofState, DecoderParser.resetCounterState] using hu12
  · simpa [t, Store.ofState, DecoderParser.resetCounterState] using hu13
  · refine ⟨huf.1, huf.2.1, huf.2.2.1, huf.2.2.2.1, ?_, huf.2.2.2.2.2⟩
    intro i h10 h12 h13
    simpa [t, Store.ofState, DecoderParser.resetCounterState, h10] using huf.2.2.2.2.1 i h10 h12 h13

def entryCode : Code := .seq readCode (.seq normalizeCode logCode)

/-- Read, normalize, round, and serialize one actual RHS coefficient. -/
theorem entry_executes (q : ℚ) (scaleNum scaleDen precision B : ℕ)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 →
      (NormalizeCoefficient.values (Codec.RationalPair.canonical q) scaleNum scaleDen precision i).bits.length ≤ B)
    (houtput : (numerator scaleNum scaleDen precision q).natAbs.bits.length ≤ B)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length) (hready : Ready s.val)
    (hscaleN : Word s.val 86 scaleNum) (hscaleD : Word s.val 87 scaleDen)
    (hpower : Word s.val 82 (2^precision)) (harchive : s.val.tapes 88 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ 120000*(B+2)^2 ∧
      Executes (preceding ++ (Codec.rat q ++ suffix)) tape entryCode cost s t ∧
      t.val.inputHead = s.val.inputHead+(Codec.rat q).length ∧
      t.val.tapes 88 = BitTape.atEnd (archive ++ record scaleNum scaleDen precision q) ∧
      Ready t.val ∧ Frame s.val t.val := by
  let input := preceding ++ (Codec.rat q ++ suffix)
  obtain ⟨a, ea, hahead, ha10, ha12, ha13, hasign, haf⟩ := reads q preceding suffix tape s hhead hready.parser
  have ak (i : ℕ) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13) : a.val.tapes i = s.val.tapes i :=
    haf.2.2.2.2.1 i h10 h12 h13
  have ab : Bank a.val (fun _ => 0) := by
    intro i hi hj
    exact word_of_eq (ak i (by omega) (by omega) (by omega)) (hready.bank i hi hj)
  have ar : Scratch a.val 0 :=
    ⟨blank_of_eq (ak 0 (by decide) (by decide) (by decide)) hready.scratch.1,
      word_of_eq (ak 1 (by decide) (by decide) (by decide)) hready.scratch.2.1,
      blank_of_eq (ak 2 (by decide) (by decide) (by decide)) hready.scratch.2.2.1,
      blank_of_eq (ak 3 (by decide) (by decide) (by decide)) hready.scratch.2.2.2⟩
  obtain ⟨c, b, hc, eb, hbout, hbb, hbr, hb12, hb13, hbf⟩ := normalizes input tape
    (Codec.RationalPair.canonical q) scaleNum scaleDen precision B hscaleNum hscaleDen hbits
    a ab ar (blank_of_eq (ak 4 (by decide) (by decide) (by decide)) hready.four)
    ha12 ha13 hasign
    (word_of_eq (ak 86 (by decide) (by decide) (by decide)) hscaleN)
    (word_of_eq (ak 87 (by decide) (by decide) (by decide)) hscaleD)
    (word_of_eq (ak 82 (by decide) (by decide) (by decide)) hpower)
  have hbout' : SignedRound.Output b.val (numerator scaleNum scaleDen precision q) := by
    simpa only [numerator, Codec.RationalPair.canonical_value] using hbout
  have bk (i : ℕ) (hi : 5 ≤ i) (h12 : i ≠ 12) (h13 : i ≠ 13) (hb : i < 30 ∨ 36 < i) :
      b.val.tapes i = a.val.tapes i := hbf.2.2.2.2.2.1 i hi h12 h13 hb
  obtain ⟨t, et, htlog, ht4, ht12, htf⟩ := logs input tape (numerator scaleNum scaleDen precision q)
    archive b hbout' hb12
    ((bk 88 (by decide) (by decide) (by decide) (Or.inr (by decide))).trans
      ((ak 88 (by decide) (by decide) (by decide)).trans harchive))
  refine ⟨_, t, ?_, ea.seq (eb.seq et), htf.inputHead.trans (hbf.2.1.trans hahead), htlog, ?_, ?_⟩
  · have hn := hbits 30 (by decide) (by decide)
    have hd := hbits 31 (by decide) (by decide)
    simp [NormalizeCoefficient.values, Codec.RationalPair.canonical] at hn hd
    nlinarith
  · refine ⟨?_, ?_, ht4, ?_⟩
    · intro i hi hj
      exact word_of_eq (htf.tapes i (by simp [logWork]; omega)) (hbb i hi hj)
    · exact ⟨blank_of_eq (htf.tapes 0 (by decide)) hbr.1,
        word_of_eq (htf.tapes 1 (by decide)) hbr.2.1,
        blank_of_eq (htf.tapes 2 (by decide)) hbr.2.2.1,
        blank_of_eq (htf.tapes 3 (by decide)) hbr.2.2.2⟩
    · exact ⟨(htf.tapes 10 (by decide)).trans
          ((bk 10 (by decide) (by decide) (by decide) (Or.inl (by decide))).trans ha10),
        ht12, (htf.tapes 13 (by decide)).trans hb13⟩
  · refine ⟨htf.memory.trans (hbf.2.2.1.trans haf.2.1),
      htf.randomCursor.trans (hbf.2.2.2.1.trans haf.2.2.1),
      htf.output.trans (hbf.2.2.2.2.1.trans haf.2.2.2.1), ?_⟩
    intro i hi
    simp only [work, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact (htf.tapes i (by simp [logWork]; omega)).trans
      ((bk i (by omega) (by omega) (by omega) (by omega)).trans
        (ak i (by omega) (by omega) (by omega)))

end Maxwell.Cost.NormalizeSource.Rhs
