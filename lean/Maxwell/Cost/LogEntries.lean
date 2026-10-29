import Maxwell.Cost.LogEntry
import Maxwell.Cost.CountedLoop

/-! A physical binary countdown controls repeated sparse-entry parsing.
The accumulated tape log retains every canonical field, and the bound sums
the actual word widths rather than multiplying by a largest-record bound. -/

namespace Maxwell.Cost.LogEntries

abbrev Entry := ℕ × ℕ × ℚ

def encodeEntry (p : Entry) : List Bool := ParseEntry.encode p.1 p.2.1 p.2.2
def records (entries : List Entry) : List Bool := entries.flatMap encodeEntry
def widths (entries : List Entry) : ℕ :=
  (entries.map fun p => LogEntry.width p.1 p.2.1 p.2.2).sum
def price (counterBits : List Bool) (entries : List Entry) : ℕ :=
  (entries.length + 1) * (13 * counterBits.length + 13) + 45 * widths entries + 168 * entries.length

def program : BitRAM := CountedLoop.program LogEntry.program

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 14 → i ≠ 15 → i ≠ 16 → i ≠ 18 →
    t.tapes i = s.tapes i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  refine ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, ?_⟩
  intro i h10 h12 h13 h14 h15 h16 h18
  exact (k.2.2.2.2 i h10 h12 h13 h14 h15 h16 h18).trans
    (h.2.2.2.2 i h10 h12 h13 h14 h15 h16 h18)

theorem frame_counter {s t : BitRAMState} (h : Counter.FrameAt 14 s t) : Frame s t := by
  refine ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro i _ _ _ hi _ _ _
  exact h.2.2.2.2.2.1 i hi

theorem frame_entry {s t : BitRAMState} (h : LogEntry.Frame s t) : Frame s t := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro i h10 h12 h13 _ h15 h16 h18
  exact h.2.2.2.2.1 i h10 h12 h13 h15 h16 h18

theorem ready_counter {s t : BitRAMState} (h : Counter.FrameAt 14 s t)
    (hs : LogEntry.Ready s) : LogEntry.Ready t := by
  exact ⟨(h.2.2.2.2.2.1 10 (by decide)).trans hs.1,
    (h.2.2.2.2.2.1 15 (by decide)).trans hs.2.1,
    (h.2.2.2.2.2.1 16 (by decide)).trans hs.2.2.1,
    (h.2.2.2.2.2.1 12 (by decide)).trans hs.2.2.2.1,
    (h.2.2.2.2.2.1 13 (by decide)).trans hs.2.2.2.2⟩

theorem steps (entries : List Entry) (counterBits : List Bool)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length)
    (hvalue : addressValue counterBits = entries.length)
    (hcounter : initial.tapes 14 = BitTape.ofList counterBits)
    (hready : LogEntry.Ready initial) (hlog : initial.tapes 18 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      PricedSteps (program.next (preceding ++ (records entries ++ suffix)) tape)
        (price counterBits entries) initial final ∧
      final.pc = CountedLoop.exitPC LogEntry.program ∧
      final.inputHead = initial.inputHead + (records entries).length ∧
      final.tapes 18 = BitTape.atEnd (archive ++ records entries) ∧
      LogEntry.Ready final ∧ Frame initial final := by
  induction entries generalizing initial counterBits preceding archive with
  | nil =>
    obtain ⟨s, hs, hspc, _, hzero, hframe⟩ :=
      CountedLoop.counter_phase LogEntry.program (preceding ++ (records [] ++ suffix)) tape
        counterBits initial hpc hcounter
    have hflag := hzero.mpr hvalue
    refine ⟨s, ?_, ?_, ?_, ?_, ready_counter hframe hready, frame_counter hframe⟩
    · simpa [price, widths, program] using hs
    · simpa [hflag] using hspc
    · simpa [records] using hframe.2.1
    · simpa [records] using (hframe.2.2.2.2.2.1 18 (by decide)).trans hlog
  | cons p entries ih =>
    let input := preceding ++ (records (p :: entries) ++ suffix)
    obtain ⟨s, hs, hspc, hsword, hzero, hframe⟩ :=
      CountedLoop.counter_phase LogEntry.program input tape counterBits initial hpc hcounter
    have hflag : s.registers 2 = false := by
      apply Bool.eq_false_iff.mpr
      intro hf
      have hv := hzero.mp hf
      simp only [List.length_cons] at hvalue
      omega
    have hbodyPC : s.pc = 17 := by simpa [hflag] using hspc
    have hpred : addressValue (subtractBit true counterBits) = entries.length := by
      rw [subtractBit_pred counterBits (by simp [hvalue]), hvalue]
      simp
    have hbodyHead : s.inputHead = preceding.length := hframe.2.1.trans hhead
    have hbodyLog : s.tapes 18 = BitTape.atEnd archive :=
      (hframe.2.2.2.2.2.1 18 (by decide)).trans hlog
    obtain ⟨t, ht, htpc, hthead, htlog, htready, htframe⟩ :=
      LogEntry.steps p.1 p.2.1 p.2.2 preceding (records entries ++ suffix) archive tape
        {s with pc := 0} rfl hbodyHead (ready_counter hframe hready) hbodyLog
    have hi : preceding ++ (ParseEntry.encode p.1 p.2.1 p.2.2 ++ (records entries ++ suffix)) = input := by
      simp [input, records, encodeEntry, List.append_assoc]
    rw [hi] at ht
    have hb := CountedLoop.body_phase LogEntry.program input tape hbodyPC ht
      (by simpa [htpc] using LogEntry.halt_instruction)
    have htword : t.tapes 14 = BitTape.ofList (subtractBit true counterBits) :=
      (htframe.2.2.2.2.1 14 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans hsword
    have hnextHead : t.inputHead = (preceding ++ encodeEntry p).length := by
      simpa [encodeEntry, hbodyHead] using hthead
    obtain ⟨final, hf, hfpc, hfhead, hflog, hfready, hfframe⟩ :=
      ih (subtractBit true counterBits) (preceding ++ encodeEntry p)
        (archive ++ encodeEntry p) {t with pc := 0} rfl hnextHead hpred htword htready htlog
    have hnextInput : (preceding ++ encodeEntry p) ++ (records entries ++ suffix) = input := by
      simp [input, records, List.append_assoc]
    rw [hnextInput] at hf
    refine ⟨final, ?_, hfpc, ?_, ?_, hfready,
      ((frame_counter hframe).trans (frame_entry htframe)).trans hfframe⟩
    · change PricedSteps (program.next input tape) _ _ _ at hs hb
      change PricedSteps (program.next input tape) _ initial final
      convert (hs.trans hb).trans hf using 1
      simp only [price, widths, List.length_cons, List.map_cons, List.sum_cons,
        subtractBit_length]
      ring
    · simp only [records, List.flatMap_cons, List.length_append] at *
      dsimp only [encodeEntry] at *
      omega
    · simpa [records, List.append_assoc] using hflog

theorem run (entries : List Entry) (counterBits : List Bool)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length)
    (hvalue : addressValue counterBits = entries.length)
    (hcounter : initial.tapes 14 = BitTape.ofList counterBits)
    (hready : LogEntry.Ready initial) (hlog : initial.tapes 18 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      (runPriced (program.next (preceding ++ (records entries ++ suffix)) tape)
        (price counterBits entries + 1) initial).finished = some final ∧
      (runPriced (program.next (preceding ++ (records entries ++ suffix)) tape)
        (price counterBits entries + 1) initial).instructions = price counterBits entries ∧
      final.inputHead = initial.inputHead + (records entries).length ∧
      final.tapes 18 = BitTape.atEnd (archive ++ records entries) ∧
      LogEntry.Ready final ∧ Frame initial final := by
  obtain ⟨final, hf, hpc', hh, hl, hr, hframe⟩ := steps entries counterBits preceding suffix archive
    tape initial hpc hhead hvalue hcounter hready hlog
  obtain ⟨hfinished, hcost⟩ := hf.runPriced (by
    simp [BitRAM.next, program, hpc', CountedLoop.exit_instruction])
  exact ⟨final, hfinished, hcost, hh, hl, hr, hframe⟩

theorem source_record_bits (S : Source.SparseSystem) :
    records (Codec.sourceRecord S).entries =
      (Codec.sourceEntries S).attach.flatMap (Codec.sourceEntry S) := by
  simp only [records, Codec.sourceRecord, List.flatMap_map]
  rfl

theorem records_length (entries : List Entry) :
    (records entries).length = 2 * widths entries + 5 * entries.length := by
  induction entries with
  | nil => simp [records, widths]
  | cons p entries ih =>
    simp only [records, List.flatMap_cons, List.length_append] at ih ⊢
    simp [encodeEntry, ParseEntry.encode, Codec.rat, Codec.int, Codec.nat,
      widths, LogEntry.width] at *
    omega

theorem price_le (counterBits : List Bool) (entries : List Entry) :
    price counterBits entries ≤
      (entries.length + 1) * (13 * counterBits.length + 13) + 34 * (records entries).length := by
  rw [records_length]
  dsimp [price]
  omega

end Maxwell.Cost.LogEntries
