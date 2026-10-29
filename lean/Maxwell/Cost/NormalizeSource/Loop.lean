import Maxwell.Cost.NormalizeSource.Entry
import Maxwell.Cost.LogEntries
import Maxwell.Cost.Structured.Counted

namespace Maxwell.Cost.NormalizeSource
open Structured RationalAccumulator

abbrev Entry := LogEntries.Entry

def Width (scaleNum scaleDen precision B : ℕ) (p : Entry) : Prop :=
  p.1.bits.length ≤ B ∧ p.2.1.bits.length ≤ B ∧
  (∀ i, 30 ≤ i → i ≤ 34 →
    (NormalizeCoefficient.values (Codec.RationalPair.canonical p.2.2) scaleNum scaleDen precision i).bits.length ≤ B) ∧
  (roundedNumerator scaleNum scaleDen precision p.2.2).natAbs < 2^precision

def records (scaleNum scaleDen precision : ℕ) (entries : List Entry) : List Bool :=
  entries.flatMap (fun p => record scaleNum scaleDen precision p.1 p.2.1 p.2.2)

def loopCode : Code := Counted.code 74 entryCode

def loopPrice (counterBits : List Bool) (entries : List Entry) (B : ℕ) : ℕ :=
  (entries.length+1)*(13*counterBits.length+15)+entries.length*(130000*(B+2)^2)

structure LoopFrame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ≠ 74 → i ∉ work → t.tapes i = s.tapes i

theorem LoopFrame.trans {s t u : BitRAMState} (h : LoopFrame s t) (k : LoopFrame t u) :
    LoopFrame s u :=
  ⟨k.memory.trans h.memory, k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i h74 hi => (k.tapes i h74 hi).trans (h.tapes i h74 hi)⟩

private theorem counter_ready {s t : Store} (h : Counted.Frame 74 s t) (hr : Ready s.val) :
    Ready t.val := by
  have ht := h.2.2.2.2.2.1
  refine ⟨?_, ?_, blank_of_eq (ht 4 (by decide)) hr.four,
    blank_of_eq (ht 83 (by decide)) hr.coefficient, ?_⟩
  · intro i hi hj
    exact word_of_eq (ht i (by omega)) (hr.bank i hi hj)
  · exact ⟨blank_of_eq (ht 0 (by decide)) hr.scratch.1,
      word_of_eq (ht 1 (by decide)) hr.scratch.2.1,
      blank_of_eq (ht 2 (by decide)) hr.scratch.2.2.1,
      blank_of_eq (ht 3 (by decide)) hr.scratch.2.2.2⟩
  · exact ⟨(ht 10 (by decide)).trans hr.parser.1,
      (ht 15 (by decide)).trans hr.parser.2.1,
      (ht 16 (by decide)).trans hr.parser.2.2.1,
      (ht 12 (by decide)).trans hr.parser.2.2.2.1,
      (ht 13 (by decide)).trans hr.parser.2.2.2.2⟩

private theorem counter_frame {s t : Store} (h : Counted.Frame 74 s t) : LoopFrame s.val t.val :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun i h74 _ => h.2.2.2.2.2.1 i h74⟩

private theorem body_frame {s t : BitRAMState} (h : Frame s t) : LoopFrame s t :=
  ⟨h.memory, h.randomCursor, h.output, fun i _ hi => h.tapes i hi⟩

/-- A fixed finite binary-counted loop normalizes precisely the stored
sparse records, with no dense matrix traversal. -/
theorem loop_executes (entries : List Entry) (scaleNum scaleDen precision B : ℕ)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hwidth : ∀ p ∈ entries, Width scaleNum scaleDen precision B p)
    (counterBits preceding suffix archive : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length)
    (hvalue : addressValue counterBits = entries.length)
    (hcounter : s.val.tapes 74 = BitTape.ofList counterBits)
    (hready : Ready s.val) (hscaleN : Word s.val 80 scaleNum)
    (hscaleD : Word s.val 81 scaleDen) (hpower : Word s.val 82 (2^precision))
    (harchive : s.val.tapes 85 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ loopPrice counterBits entries B ∧
      Executes (preceding ++ (LogEntries.records entries ++ suffix)) tape loopCode cost s t ∧
      t.val.inputHead = s.val.inputHead+(LogEntries.records entries).length ∧
      t.val.tapes 85 = BitTape.atEnd (archive ++ records scaleNum scaleDen precision entries) ∧
      Ready t.val ∧ LoopFrame s.val t.val := by
  induction entries generalizing counterBits preceding archive s with
  | nil =>
    obtain ⟨t, et, _, hz, hf⟩ := Counted.test_executes 74
      (preceding ++ (LogEntries.records [] ++ suffix)) tape s counterBits hcounter
    refine ⟨13*counterBits.length+15, t, by simp [loopPrice],
      et.seq (Executes.done (hz.mpr hvalue)), ?_, ?_, counter_ready hf hready, counter_frame hf⟩
    · simpa [LogEntries.records] using hf.2.1
    · simpa [records] using (hf.2.2.2.2.2.1 85 (by decide)).trans harchive
  | cons p entries ih =>
    let input := preceding ++ (LogEntries.records (p::entries) ++ suffix)
    obtain ⟨tested, et, htword, hz, htf⟩ := Counted.test_executes 74 input tape s counterBits hcounter
    have hpred : addressValue (subtractBit true counterBits) = entries.length := by
      rw [subtractBit_pred counterBits (by simp [hvalue]), hvalue]
      simp
    have htrue : tested.val.registers 29 = true := by
      cases h : tested.val.registers 29 with
      | true => rfl
      | false => have := hz.mp h; simp only [List.length_cons] at hvalue; omega
    have hwt := htf.2.2.2.2.2.1
    have hp := hwidth p (by simp)
    obtain ⟨c, middle, hc, em, hmhead, hmlog, hmready, hmf⟩ := entry_executes
      p.1 p.2.1 p.2.2 scaleNum scaleDen precision B hscaleNum hscaleDen
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 preceding (LogEntries.records entries ++ suffix) archive tape
      tested (htf.2.1.trans hhead) (counter_ready htf hready)
      (word_of_eq (hwt 80 (by decide)) hscaleN) (word_of_eq (hwt 81 (by decide)) hscaleD)
      (word_of_eq (hwt 82 (by decide)) hpower) ((hwt 85 (by decide)).trans harchive)
    have hi : preceding ++ (ParseEntry.encode p.1 p.2.1 p.2.2 ++
        (LogEntries.records entries ++ suffix)) = input := by
      simp [input, LogEntries.records, LogEntries.encodeEntry, List.append_assoc]
    rw [hi] at em
    have hmword : middle.val.tapes 74 = BitTape.ofList (subtractBit true counterBits) :=
      (hmf.tapes 74 (by decide)).trans htword
    have hmiddlehead : middle.val.inputHead = (preceding ++ LogEntries.encodeEntry p).length := by
      simpa [htf.2.1, hhead, LogEntries.encodeEntry] using hmhead
    obtain ⟨c', t, hc', erest, hthead, htlog, htready, hff⟩ := ih
      (fun p hp => hwidth p (by simp [hp])) (subtractBit true counterBits)
      (preceding ++ LogEntries.encodeEntry p)
      (archive ++ record scaleNum scaleDen precision p.1 p.2.1 p.2.2) middle hmiddlehead hpred hmword hmready
      (word_of_eq ((hmf.tapes 80 (by decide)).trans (hwt 80 (by decide))) hscaleN)
      (word_of_eq ((hmf.tapes 81 (by decide)).trans (hwt 81 (by decide))) hscaleD)
      (word_of_eq ((hmf.tapes 82 (by decide)).trans (hwt 82 (by decide))) hpower) hmlog
    have hi' : (preceding ++ LogEntries.encodeEntry p) ++ (LogEntries.records entries ++ suffix) = input := by
      simp [input, LogEntries.records, LogEntries.encodeEntry, List.append_assoc]
    rw [hi'] at erest
    change Executes input tape (.seq (Counted.test 74) (.loop 29 (.seq entryCode (Counted.test 74))))
      c' middle t at erest
    cases erest with
    | seq restTest restLoop =>
      refine ⟨_, t, ?_, et.seq (Executes.more htrue (em.seq restTest) restLoop), ?_, ?_, htready,
        ((counter_frame htf).trans (body_frame hmf)).trans hff⟩
      · dsimp [loopPrice] at hc' ⊢
        simp only [subtractBit_length] at hc' ⊢
        nlinarith
      · simp only [LogEntries.records, List.flatMap_cons, List.length_append] at *
        dsimp only [LogEntries.encodeEntry] at *
        omega
      · simpa [records, List.append_assoc] using htlog

end Maxwell.Cost.NormalizeSource
