import Maxwell.Cost.SourceGrouping.Entry
import Maxwell.Cost.LogEntries

namespace Maxwell.Cost.SourceGrouping

/-- One boundary bit per sparse record, from actual binary row words. -/
def markers : List Bool → Bool → List LogEntries.Entry → List Bool
  | _, _, [] => []
  | previous, seen, p :: ps =>
      (!((p.1.bits == previous) && seen)) :: markers p.1.bits true ps

def lastWord : List Bool → List LogEntries.Entry → List Bool
  | previous, [] => previous
  | _, p :: ps => lastWord p.1.bits ps

def finalSeen (seen : Bool) (entries : List LogEntries.Entry) : Bool :=
  if entries.isEmpty then seen else true

@[simp] theorem markers_length (previous : List Bool) (seen : Bool) (entries : List LogEntries.Entry) :
    (markers previous seen entries).length = entries.length := by
  induction entries generalizing previous seen with
  | nil => rfl
  | cons p ps ih => simpa [markers] using ih p.1.bits true

namespace Loop

def program : BitRAM := CountedLoop.program Entry.program

def price (counterBits previous : List Bool) (entries : List LogEntries.Entry) : ℕ :=
  (entries.length + 1) * (13 * counterBits.length + 13) +
    105 * LogEntries.widths entries + 231 * entries.length + 30 * previous.length

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 14 → i ≠ 15 → i ≠ 16 → i ≠ 18 →
    i ≠ 22 → i ≠ 24 → t.tapes i = s.tapes i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  refine ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, ?_⟩
  intro i h10 h12 h13 h14 h15 h16 h18 h22 h24
  exact (k.2.2.2.2 i h10 h12 h13 h14 h15 h16 h18 h22 h24).trans
    (h.2.2.2.2 i h10 h12 h13 h14 h15 h16 h18 h22 h24)

theorem frame_counter {s t : BitRAMState} (h : Counter.FrameAt 14 s t) : Frame s t :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun i _ _ _ hi _ _ _ _ _ => h.2.2.2.2.2.1 i hi⟩

theorem frame_entry {s t : BitRAMState} (h : Entry.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun i h10 h12 h13 _ h15 h16 h18 h22 h24 => h.2.2.2.2 i h10 h12 h13 h15 h16 h18 h22 h24⟩

/-- The loop count is a physical binary word, not an instruction parameter.
Each parsed coefficient is retained exactly and receives one row-start bit. -/
theorem steps (entries : List LogEntries.Entry) (counterBits previous : List Bool) (seen : Bool)
    (preceding suffix archive boundaries : List Bool) (tape : ℕ → Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length)
    (hvalue : addressValue counterBits = entries.length)
    (hcounter : initial.tapes 14 = BitTape.ofList counterBits)
    (hready : LogEntry.Ready initial) (hlog : initial.tapes 18 = BitTape.atEnd archive)
    (hprevious : initial.tapes 22 = BitTape.atEnd previous)
    (hboundaries : initial.tapes 24 = BitTape.atEnd boundaries)
    (hseen : initial.registers 33 = seen) :
    ∃ (cost : ℕ) (final : BitRAMState),
      cost ≤ price counterBits previous entries ∧
      PricedSteps (program.next (preceding ++ (LogEntries.records entries ++ suffix)) tape)
        cost initial final ∧
      final.pc = CountedLoop.exitPC Entry.program ∧
      final.inputHead = initial.inputHead + (LogEntries.records entries).length ∧
      final.tapes 18 = BitTape.atEnd (archive ++ LogEntries.records entries) ∧
      final.tapes 22 = BitTape.atEnd (lastWord previous entries) ∧
      final.tapes 24 = BitTape.atEnd (boundaries ++ markers previous seen entries) ∧
      final.registers 33 = finalSeen seen entries ∧
      LogEntry.Ready final ∧ Frame initial final := by
  induction entries generalizing initial counterBits previous seen preceding archive boundaries with
  | nil =>
    obtain ⟨s, hs, hspc, _, hzero, hframe⟩ := CountedLoop.counter_phase Entry.program
      (preceding ++ (LogEntries.records [] ++ suffix)) tape counterBits initial hpc hcounter
    have hflag := hzero.mpr hvalue
    refine ⟨13 * counterBits.length + 13, s, ?_, hs, ?_, ?_, ?_, ?_, ?_, ?_,
      LogEntries.ready_counter hframe hready, frame_counter hframe⟩
    · simp [price, LogEntries.widths]
    · simpa [hflag] using hspc
    · simpa [LogEntries.records] using hframe.2.1
    · simpa [LogEntries.records] using (hframe.2.2.2.2.2.1 18 (by decide)).trans hlog
    · simpa [lastWord] using (hframe.2.2.2.2.2.1 22 (by decide)).trans hprevious
    · simpa [markers] using (hframe.2.2.2.2.2.1 24 (by decide)).trans hboundaries
    · simpa [finalSeen] using (hframe.2.2.2.2.2.2 33 (by decide) (by decide) (by decide)).trans hseen
  | cons p entries ih =>
    let input := preceding ++ (LogEntries.records (p :: entries) ++ suffix)
    obtain ⟨s, hs, hspc, hsword, hzero, hframe⟩ :=
      CountedLoop.counter_phase Entry.program input tape counterBits initial hpc hcounter
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
    have hbodySeen : s.registers 33 = seen :=
      (hframe.2.2.2.2.2.2 33 (by decide) (by decide) (by decide)).trans hseen
    obtain ⟨c, t, hc, ht, htpc, hthead, htlog, htprevious, htboundaries, htseen, htready, htf⟩ :=
      Entry.steps p.1 p.2.1 p.2.2 previous preceding (LogEntries.records entries ++ suffix)
        archive boundaries tape {s with pc := 0} rfl hbodyHead
        (LogEntries.ready_counter hframe hready)
        ((hframe.2.2.2.2.2.1 18 (by decide)).trans hlog)
        ((hframe.2.2.2.2.2.1 22 (by decide)).trans hprevious)
        ((hframe.2.2.2.2.2.1 24 (by decide)).trans hboundaries)
    have hi : preceding ++ (ParseEntry.encode p.1 p.2.1 p.2.2 ++
        (LogEntries.records entries ++ suffix)) = input := by
      simp [input, LogEntries.records, LogEntries.encodeEntry, List.append_assoc]
    rw [hi] at ht
    have hb := CountedLoop.body_phase Entry.program input tape hbodyPC ht
      (by simpa [htpc] using Entry.halt_instruction)
    have htword : t.tapes 14 = BitTape.ofList (subtractBit true counterBits) :=
      (htf.2.2.2.2 14 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hsword
    have hnextHead : t.inputHead = (preceding ++ LogEntries.encodeEntry p).length := by
      simpa [LogEntries.encodeEntry, hbodyHead] using hthead
    have hnextBoundaries : t.tapes 24 =
        BitTape.atEnd (boundaries ++ [!((p.1.bits == previous) && seen)]) := by
      simpa [hbodySeen] using htboundaries
    obtain ⟨c', final, hc', hf, hfpc, hfhead, hflog, hfprevious, hfboundaries, hfseen, hfready, hff⟩ :=
      ih (subtractBit true counterBits) p.1.bits true (preceding ++ LogEntries.encodeEntry p)
        (archive ++ LogEntries.encodeEntry p) (boundaries ++ [!((p.1.bits == previous) && seen)])
        {t with pc := 0} rfl hnextHead hpred htword htready htlog htprevious hnextBoundaries htseen
    have hnextInput : (preceding ++ LogEntries.encodeEntry p) ++
        (LogEntries.records entries ++ suffix) = input := by
      simp [input, LogEntries.records, List.append_assoc]
    rw [hnextInput] at hf
    refine ⟨(13 * counterBits.length + 13) + (c + 1) + c', final, ?_,
      (hs.trans hb).trans hf, hfpc, ?_, ?_, hfprevious, ?_, ?_, hfready,
      ((frame_counter hframe).trans (frame_entry htf)).trans hff⟩
    · dsimp [price] at hc' ⊢
      simp only [LogEntries.widths, List.map_cons, List.sum_cons,
        subtractBit_length] at hc' ⊢
      dsimp [LogEntry.width] at hc hc' ⊢
      nlinarith
    · simp only [LogEntries.records, List.flatMap_cons, List.length_append] at *
      dsimp only [LogEntries.encodeEntry] at *
      omega
    · simpa [LogEntries.records, List.append_assoc] using hflog
    · simpa [markers, List.append_assoc] using hfboundaries
    · simpa [finalSeen] using hfseen

end Loop
end Maxwell.Cost.SourceGrouping
