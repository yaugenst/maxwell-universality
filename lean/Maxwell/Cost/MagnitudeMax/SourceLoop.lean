import Maxwell.Cost.MagnitudeMax.Loop
import Maxwell.Cost.MagnitudeMax.SourceBody
import Maxwell.Cost.SourceGrouping.Loop
import Maxwell.Cost.Structured.Counted

namespace Maxwell.Cost.MagnitudeMax.SourceLoop

open Structured RationalAccumulator

abbrev Entry := LogEntries.Entry

def values (entries : List Entry) : List ℚ := entries.map (fun p => p.2.2)

def code : Code := Counted.code 14 SourceBody.code

def price (counterBits : List Bool) (entries : List Entry) (B : ℕ) : ℕ :=
  (entries.length + 1) * (13 * counterBits.length + 15) + entries.length * (12000 * (B + 2)^2)

def Width (B : ℕ) (p : Entry) : Prop :=
  p.1.bits.length ≤ B ∧ p.2.1.bits.length ≤ B ∧
    p.2.2.num.natAbs.bits.length ≤ B ∧ p.2.2.den.bits.length ≤ B

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 14 → i ≠ 15 → i ≠ 16 →
    i ≠ 18 → i ≠ 22 → i ≠ 24 → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1, k.2.2.2.1.trans h.2.2.2.1,
    fun i h4 h10 h12 h13 h14 h15 h16 h18 h22 h24 hb =>
      (k.2.2.2.2 i h4 h10 h12 h13 h14 h15 h16 h18 h22 h24 hb).trans
        (h.2.2.2.2 i h4 h10 h12 h13 h14 h15 h16 h18 h22 h24 hb)⟩

theorem frame_counter {s t : Store} (h : Counted.Frame 14 s t) : Frame s.val t.val :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i _ _ _ _ h14 _ _ _ _ _ _ => h.2.2.2.2.2.1 i h14⟩

theorem frame_body {s t : BitRAMState} (h : SourceBody.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun i h4 h10 h12 h13 _ h15 h16 h18 h22 h24 hb =>
      h.2.2.2.2 i h4 h10 h12 h13 h15 h16 h18 h22 h24 hb⟩

theorem ready_counter {s t : Store} (h : Counted.Frame 14 s t) (hr : LogEntry.Ready s.val) :
    LogEntry.Ready t.val :=
  ⟨(h.2.2.2.2.2.1 10 (by decide)).trans hr.1,
    (h.2.2.2.2.2.1 15 (by decide)).trans hr.2.1,
    (h.2.2.2.2.2.1 16 (by decide)).trans hr.2.2.1,
    (h.2.2.2.2.2.1 12 (by decide)).trans hr.2.2.2.1,
    (h.2.2.2.2.2.1 13 (by decide)).trans hr.2.2.2.2⟩

/-- One actual countdown traverses only stored sparse entries. It computes
magnitude, retains coefficients, and emits precisely the existing row markers. -/
theorem executes (entries : List Entry) (current : Pair) (B : ℕ) (counterBits previous : List Bool)
    (seen : Bool) (preceding suffix archive boundaries : List Bool) (tape : ℕ → Bool) (s : Store)
    (hhead : s.val.inputHead = preceding.length)
    (hvalue : addressValue counterBits = entries.length)
    (hcounter : s.val.tapes 14 = BitTape.ofList counterBits)
    (hpositive : 0 < current.2)
    (hcurrent : current.1.bits.length ≤ B ∧ current.2.bits.length ≤ B)
    (hwidth : ∀ p ∈ entries, Width B p) (hprev : previous.length ≤ B)
    (hbank : Bank s.val (bankOf current)) (hready : Scratch s.val 0)
    (hparser : LogEntry.Ready s.val) (harchive : s.val.tapes 18 = BitTape.atEnd archive)
    (hprevious : s.val.tapes 22 = BitTape.atEnd previous)
    (hboundaries : s.val.tapes 24 = BitTape.atEnd boundaries) (hseen : s.val.registers 33 = seen) :
    ∃ cost, ∃ t : Store, cost ≤ price counterBits entries B ∧
      Executes (preceding ++ (LogEntries.records entries ++ suffix)) tape code cost s t ∧
      t.val.inputHead = s.val.inputHead + (LogEntries.records entries).length ∧
      Bank t.val (bankOf (scan current (values entries))) ∧ Scratch t.val 0 ∧ LogEntry.Ready t.val ∧
      t.val.tapes 18 = BitTape.atEnd (archive ++ LogEntries.records entries) ∧
      t.val.tapes 22 = BitTape.atEnd (SourceGrouping.lastWord previous entries) ∧
      t.val.tapes 24 = BitTape.atEnd (boundaries ++ SourceGrouping.markers previous seen entries) ∧
      t.val.registers 33 = SourceGrouping.finalSeen seen entries ∧ Frame s.val t.val := by
  induction entries generalizing current counterBits previous seen preceding archive boundaries s with
  | nil =>
    obtain ⟨t, ht, _, hz, hf⟩ := Counted.test_executes 14
      (preceding ++ (LogEntries.records [] ++ suffix)) tape s counterBits hcounter
    refine ⟨13 * counterBits.length + 15, t, by simp [price],
      ht.seq (Executes.done (hz.mpr hvalue)), ?_, Loop.bank_counter hf hbank,
      Loop.scratch_counter hf hready, ready_counter hf hparser, ?_, ?_, ?_, ?_, frame_counter hf⟩
    · simpa [LogEntries.records] using hf.2.1
    · simpa [LogEntries.records] using (hf.2.2.2.2.2.1 18 (by decide)).trans harchive
    · simpa [SourceGrouping.lastWord] using (hf.2.2.2.2.2.1 22 (by decide)).trans hprevious
    · simpa [SourceGrouping.markers] using (hf.2.2.2.2.2.1 24 (by decide)).trans hboundaries
    · simpa [SourceGrouping.finalSeen] using
        (hf.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide)).trans hseen
  | cons p entries ih =>
    let input := preceding ++ (LogEntries.records (p :: entries) ++ suffix)
    obtain ⟨tested, ht, hw, hz, hf⟩ := Counted.test_executes 14 input tape s counterBits hcounter
    have hpred : addressValue (subtractBit true counterBits) = entries.length := by
      rw [subtractBit_pred counterBits (by simp [hvalue]), hvalue]
      simp
    have htrue : tested.val.registers 29 = true := by
      cases hb : tested.val.registers 29 with
      | true => rfl
      | false => have := hz.mp hb; simp only [List.length_cons] at hvalue; omega
    have htestedhead := hf.2.1.trans hhead
    have htestedseen := (hf.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide)).trans hseen
    have hpwidth := hwidth p (by simp)
    obtain ⟨c, middle, hc, hm, hmhead, hmbank, hmready, hmparser, hmlog, hmprev, hmbounds, hmseen, hmf⟩ :=
      SourceBody.executes p.1 p.2.1 p.2.2 current B previous preceding (LogEntries.records entries ++ suffix)
        archive boundaries tape tested htestedhead hpositive hcurrent hpwidth.1 hpwidth.2.1 hpwidth.2.2
        hprev (Loop.bank_counter hf hbank) (Loop.scratch_counter hf hready) (ready_counter hf hparser)
        ((hf.2.2.2.2.2.1 18 (by decide)).trans harchive)
        ((hf.2.2.2.2.2.1 22 (by decide)).trans hprevious)
        ((hf.2.2.2.2.2.1 24 (by decide)).trans hboundaries)
    have hi : preceding ++ (ParseEntry.encode p.1 p.2.1 p.2.2 ++ (LogEntries.records entries ++ suffix)) = input := by
      simp [input, LogEntries.records, LogEntries.encodeEntry, List.append_assoc]
    rw [hi] at hm
    have hmiddlehead : middle.val.inputHead = (preceding ++ LogEntries.encodeEntry p).length := by
      simpa [htestedhead, LogEntries.encodeEntry] using hmhead
    have hmiddleword : middle.val.tapes 14 = BitTape.ofList (subtractBit true counterBits) :=
      (hmf.2.2.2.2 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (Or.inl (by decide))).trans hw
    have hmiddlebounds : middle.val.tapes 24 =
        BitTape.atEnd (boundaries ++ [!((p.1.bits == previous) && seen)]) := by
      simpa [htestedseen] using hmbounds
    obtain ⟨c', t, hc', hrest, hthead, htbank, htready, htparser, htlog, htprev, htbounds, htseen, htf⟩ :=
      ih (select current p.2.2) (subtractBit true counterBits) p.1.bits true
        (preceding ++ LogEntries.encodeEntry p) (archive ++ LogEntries.encodeEntry p)
        (boundaries ++ [!((p.1.bits == previous) && seen)]) middle hmiddlehead hpred hmiddleword
        (select_pos current p.2.2 hpositive) (select_width current p.2.2 B hcurrent hpwidth.2.2)
        (fun r hr => hwidth r (by simp [hr])) hpwidth.1 hmbank hmready hmparser hmlog hmprev hmiddlebounds hmseen
    have hi' : (preceding ++ LogEntries.encodeEntry p) ++ (LogEntries.records entries ++ suffix) = input := by
      simp [input, LogEntries.records, List.append_assoc]
    rw [hi'] at hrest
    change Executes input tape (.seq (Counted.test 14) (.loop 29 (.seq SourceBody.code (Counted.test 14))))
      c' middle t at hrest
    cases hrest with
    | seq restTest restLoop =>
      refine ⟨_, t, ?_, ht.seq (Executes.more htrue (hm.seq restTest) restLoop), ?_,
        htbank, htready, htparser, ?_, htprev, ?_, ?_,
        ((frame_counter hf).trans (frame_body hmf)).trans htf⟩
      · dsimp [price] at hc' ⊢
        simp only [subtractBit_length] at hc' ⊢
        nlinarith
      · simp only [LogEntries.records, List.flatMap_cons, List.length_append] at *
        dsimp only [LogEntries.encodeEntry] at *
        omega
      · simpa [LogEntries.records, List.append_assoc] using htlog
      · simpa [SourceGrouping.markers, List.append_assoc] using htbounds
      · simpa [SourceGrouping.finalSeen] using htseen

end Maxwell.Cost.MagnitudeMax.SourceLoop
