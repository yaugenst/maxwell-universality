import Maxwell.Cost.WordTransfer
import Maxwell.Cost.NormalizeWord

namespace Maxwell.Cost.StoredAdd

set_option maxHeartbeats 2000000

theorem max_length_le_addBits (carry : Bool) (xs ys : List Bool) :
    max xs.length ys.length ≤ (addBits carry xs ys).length := by
  induction xs generalizing ys carry with
  | nil =>
    induction ys generalizing carry with
    | nil => simp
    | cons b bs ih =>
      simp only [addBits, List.length_cons, List.length_nil, Nat.zero_max]
      exact Nat.add_le_add_right (ih _) 1
  | cons a xs ih =>
    cases ys with
    | nil =>
      simp only [addBits, List.length_cons, List.length_nil, Nat.max_zero]
      simpa only [List.length_nil, Nat.max_zero] using Nat.add_le_add_right (ih _ []) 1
    | cons b ys =>
      simp only [addBits, List.length_cons, max_add_add_right]
      exact Nat.add_le_add_right (ih _ _) 1

def program (storage : ℕ) : BitRAM := ⟨
  ((WordTransfer.move storage 0).code.map (BitRAMInstruction.relocate 0 14)) ++
  [.literal 2 false] ++
  (rippleAdder.code.map (BitRAMInstruction.relocate 15 33)) ++
  ((RewindOvershoot.program 0).code.map (BitRAMInstruction.relocate 33 42)) ++
  ((TapeOps.clear 0).code.map (BitRAMInstruction.relocate 42 48)) ++
  ((RewindOvershoot.program 1).code.map (BitRAMInstruction.relocate 48 57)) ++
  ((Rewind.program 2).code.map (BitRAMInstruction.relocate 57 62)) ++
  ((NormalizeWord.program 2).code.map (BitRAMInstruction.relocate 62 82)) ++
  ((WordTransfer.move 2 storage).code.map (BitRAMInstruction.relocate 82 96)) ++ [.halt]⟩

theorem contains_moveIn (storage : ℕ) :
    (program storage).Contains (WordTransfer.move storage 0) 0 14 := by
  intro i; fin_cases i <;> rfl

theorem contains_add (storage : ℕ) :
    (program storage).Contains rippleAdder 15 33 := by
  intro i; fin_cases i <;> rfl

theorem contains_zero (storage : ℕ) :
    (program storage).Contains (RewindOvershoot.program 0) 33 42 := by
  intro i; fin_cases i <;> rfl

theorem contains_clear (storage : ℕ) :
    (program storage).Contains (TapeOps.clear 0) 42 48 := by
  intro i; fin_cases i <;> rfl

theorem contains_one (storage : ℕ) :
    (program storage).Contains (RewindOvershoot.program 1) 48 57 := by
  intro i; fin_cases i <;> rfl

theorem contains_two (storage : ℕ) :
    (program storage).Contains (Rewind.program 2) 57 62 := by
  intro i; fin_cases i <;> rfl

theorem contains_normalize (storage : ℕ) :
    (program storage).Contains (NormalizeWord.program 2) 62 82 := by
  intro i; fin_cases i <;> rfl

theorem contains_moveOut (storage : ℕ) :
    (program storage).Contains (WordTransfer.move 2 storage) 82 96 := by
  intro i; fin_cases i <;> rfl

def carryStart (s : BitRAMState) : BitRAMState :=
  {s with pc := 15, registers := Function.update s.registers 2 false}

theorem carry_step (storage : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hp : s.pc = 14) :
    PricedSteps ((program storage).next input tape) 1 s (carryStart s) := by
  apply executeInstructions_sound (instructions := 1)
  simp [executeInstructions, BitRAM.next, program, hp, WordTransfer.move, TapeOps.copyClear,
    Rewind.program, BitRAMInstruction.relocate, BitRAMState.setRegister, carryStart]

def Frame (storage : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 3 ≤ i → i ≠ storage → t.tapes i = s.tapes i) ∧
  (∀ i, 12 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.trans {storage : ℕ} {s t u : BitRAMState}
    (h : Frame storage s t) (k : Frame storage t u) : Frame storage s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h3 hne => (kt i h3 hne).trans (ht i h3 hne),
    fun i h12 h24 h25 h26 h27 =>
      (kg i h12 h24 h25 h26 h27).trans (hg i h12 h24 h25 h26 h27)⟩

theorem frame_of_transfer {storage source target : ℕ} {s t : BitRAMState}
    (hsource : source = storage ∨ source < 3) (htarget : target = storage ∨ target < 3)
    (h : WordTransfer.Frame source target s t) : Frame storage s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h3 hne => ht i (by omega) (by omega),
    fun i _ h24 h25 h26 h27 => hg i h24 h25 h26 h27⟩

theorem frame_of_add {storage : ℕ} {s t : BitRAMState}
    (h : rippleFrame t = rippleFrame s) : Frame storage s t := by
  simp only [rippleFrame, Prod.mk.injEq] at h
  rcases h with ⟨ha, hi, hm, hr, ho, hg, ht⟩
  refine ⟨ha, hi, hm, hr, ho, ?_, ?_⟩
  · intro i h3 _
    simpa only [Nat.sub_add_cancel h3] using congrFun ht (i - 3)
  · intro i h12 _ _ _ _
    simpa only [Nat.sub_add_cancel h12] using congrFun hg (i - 12)

theorem frame_carry (storage : ℕ) (s : BitRAMState) : Frame storage s (carryStart s) := by
  simp [Frame, carryStart]
  intro i hi _ _ _ _
  simp [show i ≠ 2 by omega]

theorem frame_rewind (storage workTape : ℕ) (hw : workTape < 3)
    (origin : ℤ) (s : BitRAMState) :
    Frame storage s (Rewind.finishAt workTape origin s) := by
  simp [Frame, Rewind.finishAt]
  constructor
  · intro i h3 _
    simp [show i ≠ workTape by omega]
  · intro i _ h24 h25 _ _
    simp [h24, h25]

theorem frame_of_normalize {storage : ℕ} {s t : BitRAMState}
    (h : NormalizeWord.Frame 2 s t) : Frame storage s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h3 _ => ht i (by omega),
    fun i _ h24 h25 h26 h27 => hg i h24 h25 h26 h27⟩

/-- Stored unsigned addition, with canonical output and reusable blank scratch.
Nonempty padded operands include zero; `PadWord` provides this condition by
executing a read and an optional zero write. -/
theorem simulation (storage : ℕ) (hstorage : 3 ≤ storage)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool)
    (ao xo zo storageOrigin : ℤ) (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (s : BitRAMState) (hpc : s.pc = 0)
    (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (hword : s.tapes storage = BitTape.shifted ys storageOrigin) :
    ∃ cost t, cost ≤ 100 * (xs.length + ys.length + 2) ∧
      PricedSteps ((program storage).next input tape) cost s t ∧ t.pc = 96 ∧
      t.tapes storage = BitTape.shifted (addressValue xs + addressValue ys).bits
        (storageOrigin + ys.length) ∧
      t.tapes 0 = {BitTape.blank with head := ao + ys.length} ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := zo + (addressValue xs + addressValue ys).bits.length} ∧
      Frame storage s t := by
  obtain ⟨moved, hm, hmp, hmStorage, hm0, hmFrame⟩ :=
    WordTransfer.move_steps storage 0 (by omega) input tape ys storageOrigin ao
      {s with pc := 0} rfl hword h0
  let s1 : BitRAMState := {moved with pc := 14}
  have hs1 := (contains_moveIn storage).call_at input tape s moved hpc hm
    (by simp [WordTransfer.move, hmp, TapeOps.copyClear, Rewind.program,
      BitRAMInstruction.relocate])
  have hm1 : s1.tapes 1 = BitTape.shifted xs xo :=
    (hmFrame.2.2.2.2.2.1 1 (by omega) (by omega)).trans h1
  have hm2 : s1.tapes 2 = {BitTape.blank with head := zo} :=
    (hmFrame.2.2.2.2.2.1 2 (by omega) (by omega)).trans h2
  let sc := carryStart s1
  have hsc := carry_step storage input tape s1 rfl
  let raw := addBits false ys xs
  have hrawLength := addBits_length_le false ys xs
  have hrawGe := max_length_le_addBits false ys xs
  obtain ⟨addCost, added, haCost, ha, hap, ha0, ha1, ha2, haFrame⟩ :=
    rippleAdder_words input tape {sc with pc := 0} ys xs ao xo zo rfl
      (by simp [sc, carryStart]) hm0 hm1 hm2
  let s2 : BitRAMState := {added with pc := 33}
  have hs2 := (contains_add storage).call_at input tape sc added rfl ha
    (by simp [rippleAdder, hap])
  have hr0 := WordTransfer.rewind_overshoot_shifted 0 ao input tape ys raw.length hys
    (by dsimp [raw]; omega) {s2 with pc := 0} rfl ha0
  let r0 := RewindOvershoot.finish 0 ao {s2 with pc := 0}
  let s3 : BitRAMState := {r0 with pc := 42}
  have hs3 := (contains_zero storage).call_at input tape s2 r0 rfl hr0.1
    (by simp [r0, RewindOvershoot.finish, RewindOvershoot.program,
      RewindOvershoot.preamble, BitRAM.link, Rewind.finishAt, Rewind.program])
  obtain ⟨cleared, hc, hcp, hc0, hcFrame⟩ := TapeOps.clear_steps 0 input tape ys ao
    {s3 with pc := 0} rfl hr0.2
  let s4 : BitRAMState := {cleared with pc := 48}
  have hs4 := (contains_clear storage).call_at input tape s3 cleared rfl hc
    (by simp [TapeOps.clear, hcp])
  have hr01 : s3.tapes 1 = {BitTape.shifted xs xo with head := xo + raw.length} := by
    simpa [s3, r0, RewindOvershoot.finish, Rewind.finishAt] using ha1
  have hc1 : s4.tapes 1 = {BitTape.shifted xs xo with head := xo + raw.length} :=
    (hcFrame.2.2.2.2.2.1 1 (by omega) (by omega)).trans hr01
  have hr1 := WordTransfer.rewind_overshoot_shifted 1 xo input tape xs raw.length hxs
    (by dsimp [raw]; omega) {s4 with pc := 0} rfl hc1
  let r1 := RewindOvershoot.finish 1 xo {s4 with pc := 0}
  let s5 : BitRAMState := {r1 with pc := 57}
  have hs5 := (contains_one storage).call_at input tape s4 r1 rfl hr1.1
    (by simp [r1, RewindOvershoot.finish, RewindOvershoot.program,
      RewindOvershoot.preamble, BitRAM.link, Rewind.finishAt, Rewind.program])
  have hr02 : s3.tapes 2 = BitTape.shiftedEnd raw zo := by
    simpa [s3, r0, RewindOvershoot.finish, Rewind.finishAt] using ha2
  have hc2 : s4.tapes 2 = BitTape.shiftedEnd raw zo :=
    (hcFrame.2.2.2.2.2.1 2 (by omega) (by omega)).trans hr02
  have hr12 : s5.tapes 2 = BitTape.shiftedEnd raw zo := by
    simpa [s5, r1, RewindOvershoot.finish, Rewind.finishAt] using hc2
  have hr2 := WordTransfer.rewind_shifted 2 zo input tape raw {s5 with pc := 0} rfl hr12
  let r2 := Rewind.finishAt 2 zo {s5 with pc := 0}
  let s6 : BitRAMState := {r2 with pc := 62}
  have hs6 := (contains_two storage).call_at input tape s5 r2 rfl hr2.1
    (by simp [r2, Rewind.finishAt, Rewind.program])
  obtain ⟨normCost, normalized, hnCost, hn, hnp, hn2, hnLength, hnFrame⟩ :=
    NormalizeWord.simulation 2 zo input tape raw {s6 with pc := 0} rfl hr2.2
  let s7 : BitRAMState := {normalized with pc := 82}
  have hs7 := (contains_normalize storage).call_at input tape s6 normalized rfl hn
    (by simp [NormalizeWord.program, hnp, ScanForward.program, TapeOps.trim,
      Rewind.program, BitRAMInstruction.relocate])
  have hFmove : Frame storage s s1 := frame_of_transfer (Or.inl rfl) (Or.inr (by omega)) hmFrame
  have hFcarry : Frame storage s1 sc := frame_carry storage s1
  have hFadd : Frame storage sc s2 := frame_of_add haFrame
  have hFzero : Frame storage s2 s3 := frame_rewind storage 0 (by omega) ao {s2 with pc := 0}
  have hFclear : Frame storage s3 s4 := frame_of_transfer (Or.inr (by omega))
    (Or.inr (by omega)) (WordTransfer.frame_of_copy hcFrame)
  have hFone : Frame storage s4 s5 := frame_rewind storage 1 (by omega) xo {s4 with pc := 0}
  have hFtwo : Frame storage s5 s6 := frame_rewind storage 2 (by omega) zo {s5 with pc := 0}
  have hFnorm : Frame storage s6 s7 := frame_of_normalize hnFrame
  have haStorage : s2.tapes storage = {BitTape.blank with head := storageOrigin + ys.length} := by
    have ht := congrArg (fun x => x.2.2.2.2.2.2 (storage - 3)) haFrame
    have ht' : added.tapes storage = sc.tapes storage := by
      simpa [rippleFrame, Nat.sub_add_cancel hstorage] using ht
    exact ht'.trans hmStorage
  have hr0Storage : s3.tapes storage = {BitTape.blank with head := storageOrigin + ys.length} := by
    simpa [s3, r0, RewindOvershoot.finish, Rewind.finishAt, show storage ≠ 0 by omega] using haStorage
  have hcStorage : s4.tapes storage = {BitTape.blank with head := storageOrigin + ys.length} :=
    (hcFrame.2.2.2.2.2.1 storage (by omega) (by omega)).trans hr0Storage
  have hr1Storage : s5.tapes storage = {BitTape.blank with head := storageOrigin + ys.length} := by
    simpa [s5, r1, RewindOvershoot.finish, Rewind.finishAt, show storage ≠ 1 by omega] using hcStorage
  have hr2Storage : s6.tapes storage = {BitTape.blank with head := storageOrigin + ys.length} := by
    simpa [s6, r2, Rewind.finishAt, show storage ≠ 2 by omega] using hr1Storage
  have hnStorage : s7.tapes storage = {BitTape.blank with head := storageOrigin + ys.length} :=
    (hnFrame.2.2.2.2.2.1 storage (by omega)).trans hr2Storage
  let canonical := (addressValue raw).bits
  obtain ⟨stored, ho, hop, ho2, hoStorage, hoFrame⟩ :=
    WordTransfer.move_steps 2 storage (by omega) input tape canonical zo
      (storageOrigin + ys.length) {s7 with pc := 0} rfl hn2 hnStorage
  have hs8 := (contains_moveOut storage).call_at input tape s7 stored rfl ho
    (by simp [WordTransfer.move, hop, TapeOps.copyClear, Rewind.program,
      BitRAMInstruction.relocate])
  have hFout : Frame storage s7 {stored with pc := 96} :=
    frame_of_transfer (Or.inr (by omega)) (Or.inl rfl) hoFrame
  have hvalue : addressValue raw = addressValue xs + addressValue ys := by
    simp [raw, addBits_value, Nat.add_comm]
  refine ⟨(12 * ys.length + 10 + 1) + 1 + (addCost + 1) +
      (4 * raw.length + 6 + 1) + (6 * ys.length + 3 + 1) +
      (4 * raw.length + 6 + 1) + (4 * raw.length + 5 + 1) + (normCost + 1) +
      (12 * canonical.length + 10 + 1), {stored with pc := 96}, ?_,
    ((((((((hs1.trans hsc).trans hs2).trans hs3).trans hs4).trans hs5).trans hs6).trans hs7).trans hs8),
    rfl, ?_, ?_, ?_, ?_,
    ((((((((hFmove.trans hFcarry).trans hFadd).trans hFzero).trans hFclear).trans hFone).trans hFtwo).trans hFnorm).trans hFout)⟩
  · dsimp [canonical]
    have hm : max ys.length xs.length ≤ ys.length + xs.length := by omega
    have hrawBound : raw.length ≤ xs.length + ys.length + 1 := by dsimp [raw]; omega
    omega
  · simpa [canonical, hvalue] using hoStorage
  · have hr10 : s5.tapes 0 = {BitTape.blank with head := ao + ys.length} := by
      simpa [s5, r1, RewindOvershoot.finish, Rewind.finishAt] using hc0
    have hr20 : s6.tapes 0 = {BitTape.blank with head := ao + ys.length} := by
      simpa [s6, r2, Rewind.finishAt] using hr10
    have hn0 := (hnFrame.2.2.2.2.2.1 0 (by omega)).trans hr20
    exact (hoFrame.2.2.2.2.2.1 0 (by omega) (by omega)).trans hn0
  · have hr21 : s6.tapes 1 = BitTape.shifted xs xo := by
      simpa [s6, r2, Rewind.finishAt] using hr1.2
    have hn1 := (hnFrame.2.2.2.2.2.1 1 (by omega)).trans hr21
    exact (hoFrame.2.2.2.2.2.1 1 (by omega) (by omega)).trans hn1
  · simpa [canonical, hvalue] using ho2

end Maxwell.Cost.StoredAdd
