import Maxwell.Cost.LogRat
import Maxwell.Cost.CountedLoop

/-! A finite rational-list loop retains the right-hand-side records on
tape 20. Its independent physical count tape is 21. -/

namespace Maxwell.Cost.LogRats

def records (values : List ℚ) : List Bool := values.flatMap Codec.rat
def widths (values : List ℚ) : ℕ := (values.map LogRat.width).sum
def price (counterBits : List Bool) (values : List ℚ) : ℕ :=
  (values.length + 1) * (13 * counterBits.length + 13) + 45 * widths values + 87 * values.length
def rawProgram : BitRAM := CountedLoop.program LogRat.program
def permutation : Equiv.Perm ℕ := Equiv.swap 14 21
def program : BitRAM := rawProgram.renameTapes permutation

def Frame (counterTape : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ counterTape → i ≠ 20 → t.tapes i = s.tapes i)

theorem Frame.trans {counterTape : ℕ} {s t u : BitRAMState}
    (h : Frame counterTape s t) (k : Frame counterTape t u) : Frame counterTape s u := by
  refine ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, ?_⟩
  intro i h10 h12 h13 hc h20
  exact (k.2.2.2.2 i h10 h12 h13 hc h20).trans (h.2.2.2.2 i h10 h12 h13 hc h20)

theorem frame_counter {s t : BitRAMState} (h : Counter.FrameAt 14 s t) : Frame 14 s t := by
  refine ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro i _ _ _ hi _
  exact h.2.2.2.2.2.1 i hi

theorem frame_rat {s t : BitRAMState} (h : LogRat.Frame s t) : Frame 14 s t := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro i h10 h12 h13 _ h20
  exact h.2.2.2.2 i h10 h12 h13 h20

theorem ready_counter {s t : BitRAMState} (h : Counter.FrameAt 14 s t)
    (hs : LogRat.Ready s) : LogRat.Ready t := by
  exact ⟨(h.2.2.2.2.2.1 10 (by decide)).trans hs.1,
    (h.2.2.2.2.2.1 12 (by decide)).trans hs.2.1,
    (h.2.2.2.2.2.1 13 (by decide)).trans hs.2.2⟩

theorem raw_steps (values : List ℚ) (counterBits : List Bool)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length)
    (hvalue : addressValue counterBits = values.length)
    (hcounter : initial.tapes 14 = BitTape.ofList counterBits)
    (hready : LogRat.Ready initial) (hlog : initial.tapes 20 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      PricedSteps (rawProgram.next (preceding ++ (records values ++ suffix)) tape)
        (price counterBits values) initial final ∧
      final.pc = CountedLoop.exitPC LogRat.program ∧
      final.inputHead = initial.inputHead + (records values).length ∧
      final.tapes 20 = BitTape.atEnd (archive ++ records values) ∧
      LogRat.Ready final ∧ Frame 14 initial final := by
  induction values generalizing initial counterBits preceding archive with
  | nil =>
    obtain ⟨s, hs, hspc, _, hzero, hframe⟩ :=
      CountedLoop.counter_phase LogRat.program (preceding ++ (records [] ++ suffix)) tape
        counterBits initial hpc hcounter
    have hflag := hzero.mpr hvalue
    refine ⟨s, ?_, ?_, ?_, ?_, ready_counter hframe hready, frame_counter hframe⟩
    · simpa [price, widths, rawProgram] using hs
    · simpa [hflag] using hspc
    · simpa [records] using hframe.2.1
    · simpa [records] using (hframe.2.2.2.2.2.1 20 (by decide)).trans hlog
  | cons q values ih =>
    let input := preceding ++ (records (q :: values) ++ suffix)
    obtain ⟨s, hs, hspc, hsword, hzero, hframe⟩ :=
      CountedLoop.counter_phase LogRat.program input tape counterBits initial hpc hcounter
    have hflag : s.registers 2 = false := by
      apply Bool.eq_false_iff.mpr
      intro hf
      have hv := hzero.mp hf
      simp only [List.length_cons] at hvalue
      omega
    have hbodyPC : s.pc = 17 := by simpa [hflag] using hspc
    have hpred : addressValue (subtractBit true counterBits) = values.length := by
      rw [subtractBit_pred counterBits (by simp [hvalue]), hvalue]
      simp
    have hbodyHead : s.inputHead = preceding.length := hframe.2.1.trans hhead
    have hbodyLog : s.tapes 20 = BitTape.atEnd archive :=
      (hframe.2.2.2.2.2.1 20 (by decide)).trans hlog
    obtain ⟨t, ht, htpc, hthead, htlog, htready, htframe⟩ :=
      LogRat.steps q preceding (records values ++ suffix) archive tape {s with pc := 0}
        rfl hbodyHead (ready_counter hframe hready) hbodyLog
    have hi : preceding ++ (Codec.rat q ++ (records values ++ suffix)) = input := by
      simp [input, records, List.append_assoc]
    rw [hi] at ht
    have hb := CountedLoop.body_phase LogRat.program input tape hbodyPC ht
      (by simpa [htpc] using LogRat.halt_instruction)
    have htword : t.tapes 14 = BitTape.ofList (subtractBit true counterBits) :=
      (htframe.2.2.2.2 14 (by decide) (by decide) (by decide) (by decide)).trans hsword
    have hnextHead : t.inputHead = (preceding ++ Codec.rat q).length := by
      simpa [hbodyHead] using hthead
    obtain ⟨final, hf, hfpc, hfhead, hflog, hfready, hfframe⟩ :=
      ih (subtractBit true counterBits) (preceding ++ Codec.rat q)
        (archive ++ Codec.rat q) {t with pc := 0} rfl hnextHead hpred htword htready htlog
    have hnextInput : (preceding ++ Codec.rat q) ++ (records values ++ suffix) = input := by
      simp [input, records, List.append_assoc]
    rw [hnextInput] at hf
    refine ⟨final, ?_, hfpc, ?_, ?_, hfready,
      ((frame_counter hframe).trans (frame_rat htframe)).trans hfframe⟩
    · change PricedSteps (rawProgram.next input tape) _ _ _ at hs hb
      change PricedSteps (rawProgram.next input tape) _ initial final
      convert (hs.trans hb).trans hf using 1
      simp only [price, widths, List.length_cons, List.map_cons, List.sum_cons, subtractBit_length]
      ring
    · simp only [records, List.flatMap_cons, List.length_append] at *
      omega
    · simpa [records, List.append_assoc] using hflog

theorem steps (values : List ℚ) (counterBits : List Bool)
    (preceding suffix archive : List Bool) (tape : ℕ → Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length)
    (hvalue : addressValue counterBits = values.length)
    (hcounter : initial.tapes 21 = BitTape.ofList counterBits)
    (hready : LogRat.Ready initial) (hlog : initial.tapes 20 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      PricedSteps (program.next (preceding ++ (records values ++ suffix)) tape)
        (price counterBits values) initial final ∧
      final.pc = CountedLoop.exitPC LogRat.program ∧
      final.inputHead = initial.inputHead + (records values).length ∧
      final.tapes 20 = BitTape.atEnd (archive ++ records values) ∧
      LogRat.Ready final ∧ Frame 21 initial final := by
  obtain ⟨s, hs, hspc, hshead, hslog, hsready, hframe⟩ :=
    raw_steps values counterBits preceding suffix archive tape
      (initial.renameTapes permutation.symm) hpc hhead hvalue
      (by simpa [BitRAMState.renameTapes, permutation] using hcounter)
      (by simpa [LogRat.Ready, BitRAMState.renameTapes, permutation, Equiv.swap_apply_def] using hready)
      (by simpa [BitRAMState.renameTapes, permutation, Equiv.swap_apply_def] using hlog)
  have hh := hs.renameTapes permutation
  rw [BitRAMState.renameTapes_inverse] at hh
  refine ⟨s.renameTapes permutation, hh, hspc, hshead, ?_, ?_, ?_⟩
  · simpa [BitRAMState.renameTapes, permutation, Equiv.swap_apply_def] using hslog
  · simpa [LogRat.Ready, BitRAMState.renameTapes, permutation, Equiv.swap_apply_def] using hsready
  · refine ⟨hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1, ?_⟩
    intro i h10 h12 h13 h21 h20
    by_cases h14 : i = 14
    · subst i
      simpa [BitRAMState.renameTapes, permutation] using
        hframe.2.2.2.2 21 (by decide) (by decide) (by decide) (by decide) (by decide)
    · simpa [BitRAMState.renameTapes, permutation, Equiv.swap_apply_def, h14, h21] using
        hframe.2.2.2.2 i h10 h12 h13 h14 h20

theorem halt_instruction : program.code[136]? = some .halt := by decide

theorem records_length (values : List ℚ) :
    (records values).length = 2 * widths values + 3 * values.length := by
  induction values with
  | nil => simp [records, widths]
  | cons q values ih =>
    simp only [records, List.flatMap_cons, List.length_append] at ih ⊢
    simp [Codec.rat, Codec.int, Codec.nat, widths, LogRat.width] at *
    omega

theorem price_le (counterBits : List Bool) (values : List ℚ) :
    price counterBits values ≤
      (values.length + 1) * (13 * counterBits.length + 13) + 29 * (records values).length := by
  rw [records_length]
  dsimp [price]
  omega

end Maxwell.Cost.LogRats
