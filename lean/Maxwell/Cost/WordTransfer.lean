import Maxwell.Cost.Copy
import Maxwell.Cost.Scan
import Maxwell.Cost.ScanOvershoot
import Maxwell.Cost.Blocks

/-! Charged transfer routines leave operands at their first bit. This is
needed when arithmetic blocks are called repeatedly by the rational decoder. -/

namespace Maxwell.Cost.WordTransfer

def Frame (source target : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ source → i ≠ target → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.trans {source target : ℕ} {s t u : BitRAMState}
    (h : Frame source target s t) (k : Frame source target t u) : Frame source target s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hs ht' => (kt i hs ht').trans (ht i hs ht'),
    fun i h24 h25 h26 h27 => (kg i h24 h25 h26 h27).trans (hg i h24 h25 h26 h27)⟩

theorem frame_of_copy {source target : ℕ} {s t : BitRAMState}
    (h : TapeOps.Frame source target s t) : Frame source target s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, ht, fun i _ _ h26 h27 => hg i h26 h27⟩

theorem frame_rewind (source target workTape : ℕ) (hw : workTape = source ∨ workTape = target)
    (origin : ℤ) (s : BitRAMState) : Frame source target s (Rewind.finishAt workTape origin s) := by
  simp [Frame, Rewind.finishAt]
  constructor
  · intro i hs ht
    simp [show i ≠ workTape by omega]
  · intro i h24 h25 _ _
    simp [h24, h25]

theorem rewind_shifted (workTape : ℕ) (origin : ℤ) (input : List Bool)
    (tape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = BitTape.shiftedEnd bits origin) :
    PricedSteps ((Rewind.program workTape).next input tape) (4 * bits.length + 5) s
      (Rewind.finishAt workTape origin s) ∧
      (Rewind.finishAt workTape origin s).tapes workTape = BitTape.shifted bits origin := by
  constructor
  · exact Rewind.stepsAt workTape origin input tape bits.length s hpc
      (by simp [hword, BitTape.shiftedEnd])
      (by simp [hword, BitTape.shiftedEnd, BitTape.shifted])
      (by
        intro k hk
        refine ⟨bits[k], ?_⟩
        simp [hword, BitTape.shiftedEnd, BitTape.shifted, hk])
  · simp [Rewind.finishAt, hword, BitTape.shiftedEnd, BitTape.shifted]

theorem rewind_overshoot_shifted (workTape : ℕ) (origin : ℤ) (input : List Bool)
    (tape : ℕ → Bool) (bits : List Bool) (distance : ℕ) (hbits : 0 < bits.length)
    (hdistance : bits.length ≤ distance) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = {BitTape.shifted bits origin with head := origin + distance}) :
    PricedSteps ((RewindOvershoot.program workTape).next input tape) (4 * distance + 6) s
      (RewindOvershoot.finish workTape origin s) ∧
      (RewindOvershoot.finish workTape origin s).tapes workTape = BitTape.shifted bits origin := by
  constructor
  · have hs := RewindOvershoot.steps workTape origin input tape bits.length
      (distance - bits.length) hbits s hpc
      (by simp [hword]; omega)
      (by simp [hword, BitTape.shifted])
      (by
        intro k hk
        refine ⟨bits[k], ?_⟩
        simp [hword, BitTape.shifted, hk])
      (by
        intro k _
        simp [hword, BitTape.shifted]
        omega)
    simpa only [Nat.add_sub_of_le hdistance] using hs
  · simp [RewindOvershoot.finish, Rewind.finishAt, hword, BitTape.shifted]

def move (source target : ℕ) : BitRAM := ⟨
  ((TapeOps.copyClear source target).code.map (BitRAMInstruction.relocate 0 8)) ++
  ((Rewind.program target).code.map (BitRAMInstruction.relocate 8 13)) ++ [.halt]⟩

theorem move_copy (source target : ℕ) :
    (move source target).Contains (TapeOps.copyClear source target) 0 8 := by
  intro i
  fin_cases i <;> rfl

theorem move_rewind (source target : ℕ) :
    (move source target).Contains (Rewind.program target) 8 13 := by
  intro i
  fin_cases i <;> rfl

theorem move_steps (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (sourceOrigin targetOrigin : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hs : s.tapes source = BitTape.shifted bits sourceOrigin)
    (ht : s.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, PricedSteps ((move source target).next input tape) (12 * bits.length + 10) s t ∧
      t.pc = 13 ∧ t.tapes source = {BitTape.blank with head := sourceOrigin + bits.length} ∧
      t.tapes target = BitTape.shifted bits targetOrigin ∧ Frame source target s t := by
  obtain ⟨copied, hc, hcp, hcs, hct, hcf⟩ :=
    TapeOps.copyClear_to_blank_steps source target hne input tape bits sourceOrigin targetOrigin
      {s with pc := 0} rfl hs ht
  have hc' := (move_copy source target).call_at input tape s copied hpc hc
    (by simp [TapeOps.copyClear, hcp])
  let s1 : BitRAMState := {copied with pc := 8}
  have hr := rewind_shifted target targetOrigin input tape bits {s1 with pc := 0} rfl hct
  let t := Rewind.finishAt target targetOrigin {s1 with pc := 0}
  have hr' := (move_rewind source target).call_at input tape s1 t rfl hr.1
    (by simp [t, Rewind.program, Rewind.finishAt])
  refine ⟨{t with pc := 13}, ?_, rfl, ?_, hr.2,
    (frame_of_copy hcf).trans (frame_rewind source target target (Or.inr rfl)
      targetOrigin {s1 with pc := 0})⟩
  · convert hc'.trans hr' using 1
    omega
  · simpa [t, Rewind.finishAt, hne] using hcs

def clone (source target : ℕ) : BitRAM := ⟨
  ((Copy.program source target).code.map (BitRAMInstruction.relocate 0 7)) ++
  ((Rewind.program source).code.map (BitRAMInstruction.relocate 7 12)) ++
  ((Rewind.program target).code.map (BitRAMInstruction.relocate 12 17)) ++ [.halt]⟩

theorem clone_copy (source target : ℕ) :
    (clone source target).Contains (Copy.program source target) 0 7 := by
  intro i
  fin_cases i <;> rfl

theorem clone_source (source target : ℕ) :
    (clone source target).Contains (Rewind.program source) 7 12 := by
  intro i
  fin_cases i <;> rfl

theorem clone_target (source target : ℕ) :
    (clone source target).Contains (Rewind.program target) 12 17 := by
  intro i
  fin_cases i <;> rfl

theorem clone_steps (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (sourceOrigin targetOrigin : ℤ)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hs : s.tapes source = BitTape.shifted bits sourceOrigin)
    (ht : s.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, PricedSteps ((clone source target).next input tape) (15 * bits.length + 16) s t ∧
      t.pc = 17 ∧ t.tapes source = BitTape.shifted bits sourceOrigin ∧
      t.tapes target = BitTape.shifted bits targetOrigin ∧ Frame source target s t := by
  obtain ⟨copied, hc, hcp, hcs, hct, hcf⟩ :=
    Copy.shifted_steps source target hne input tape bits sourceOrigin targetOrigin
      {s with pc := 0} rfl hs ht
  have hc' := (clone_copy source target).call_at input tape s copied hpc hc
    (by simp [Copy.program, hcp])
  let s1 : BitRAMState := {copied with pc := 7}
  have hr := rewind_shifted source sourceOrigin input tape bits {s1 with pc := 0} rfl hcs
  let rewound := Rewind.finishAt source sourceOrigin {s1 with pc := 0}
  let s2 : BitRAMState := {rewound with pc := 12}
  have hr' := (clone_source source target).call_at input tape s1 rewound rfl hr.1
    (by simp [rewound, Rewind.program, Rewind.finishAt])
  have ht2 : s2.tapes target = BitTape.shiftedEnd bits targetOrigin := by
    simpa [s2, rewound, Rewind.finishAt, Ne.symm hne] using hct
  have ht' := rewind_shifted target targetOrigin input tape bits {s2 with pc := 0} rfl ht2
  let t := Rewind.finishAt target targetOrigin {s2 with pc := 0}
  have hlast := (clone_target source target).call_at input tape s2 t rfl ht'.1
    (by simp [t, Rewind.program, Rewind.finishAt])
  refine ⟨{t with pc := 17}, ?_, rfl, ?_, ht'.2,
    ((frame_of_copy hcf).trans (frame_rewind source target source (Or.inl rfl)
      sourceOrigin {s1 with pc := 0})).trans
        (frame_rewind source target target (Or.inr rfl) targetOrigin {s2 with pc := 0})⟩
  · convert (hc'.trans hr').trans hlast using 1
    omega
  · simpa [t, s2, rewound, Rewind.finishAt, hne] using hr.2

end Maxwell.Cost.WordTransfer
