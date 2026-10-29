import Maxwell.Cost.Multiplication.Frame
import Maxwell.Cost.NormalizeWord

/-! A linked stored-word multiplication block for rational accumulators.
The denominator word on tape 1 is preserved. The selected stored numerator
is replaced by its product, and the integer scratch tapes are cleared.
Tape identifiers are fixed code literals, never input-dependent programs. -/

namespace Maxwell.Cost.StoredProduct

def program (storage : ℕ) : BitRAM := ⟨
  ((TapeOps.copyClear storage 3).code.map (BitRAMInstruction.relocate 0 8)) ++
  (HornerMultiply.program.code.map (BitRAMInstruction.relocate 8 80)) ++
  ((NormalizeWord.program 0).code.map (BitRAMInstruction.relocate 80 100)) ++
  ((TapeOps.copyClear 0 storage).code.map (BitRAMInstruction.relocate 100 108)) ++
  ((Rewind.program storage).code.map (BitRAMInstruction.relocate 108 113)) ++
  [.tapeRight 3] ++
  ((TapeOps.clear 3).code.map (BitRAMInstruction.relocate 114 120)) ++
  [.halt]⟩

theorem contains_input (storage : ℕ) :
    (program storage).Contains (TapeOps.copyClear storage 3) 0 8 := by
  intro i
  fin_cases i <;> rfl

theorem contains_multiply (storage : ℕ) :
    (program storage).Contains HornerMultiply.program 8 80 := by
  intro i
  fin_cases i <;> rfl

theorem contains_normalize (storage : ℕ) :
    (program storage).Contains (NormalizeWord.program 0) 80 100 := by
  intro i
  fin_cases i <;> rfl

theorem contains_output (storage : ℕ) :
    (program storage).Contains (TapeOps.copyClear 0 storage) 100 108 := by
  intro i
  fin_cases i <;> rfl

theorem contains_rewind (storage : ℕ) :
    (program storage).Contains (Rewind.program storage) 108 113 := by
  intro i
  fin_cases i <;> rfl

theorem contains_clear (storage : ℕ) :
    (program storage).Contains (TapeOps.clear 3) 114 120 := by
  intro i
  fin_cases i <;> rfl

def Frame (storage : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ storage → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.trans {storage : ℕ} {s t u : BitRAMState}
    (h : Frame storage s t) (k : Frame storage t u) : Frame storage s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h4 hne => (kt i h4 hne).trans (ht i h4 hne),
    fun i h15 h24 h25 h26 h27 =>
      (kg i h15 h24 h25 h26 h27).trans (hg i h15 h24 h25 h26 h27)⟩

theorem frame_of_copy {storage source target : ℕ} {s t : BitRAMState}
    (hsource : source = storage ∨ source < 4) (htarget : target = storage ∨ target < 4)
    (h : TapeOps.Frame source target s t) : Frame storage s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  refine ⟨ha, hi, hm, hr, ho, ?_, ?_⟩
  · intro i h4 hne
    exact ht i (by omega) (by omega)
  · intro i _ _ _ h26 h27
    exact hg i h26 h27

theorem frame_of_multiply {storage : ℕ} {s t : BitRAMState}
    (h : HornerMultiply.Frame s t) : Frame storage s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 _ => ht i h4, hg⟩

theorem frame_of_normalize {storage : ℕ} {s t : BitRAMState}
    (h : NormalizeWord.Frame 0 s t) : Frame storage s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i h4 _ => ht i (by omega),
    fun i _ h24 h25 h26 h27 => hg i h24 h25 h26 h27⟩

theorem frame_rewind (storage : ℕ) (origin : ℤ) (s : BitRAMState) :
    Frame storage s (Rewind.finishAt storage origin s) := by
  simp [Frame, Rewind.finishAt]
  constructor
  · intro i _ hi
    simp [hi]
  · intro i _ h24 h25 _ _
    simp [h24, h25]

def clearStart (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update s.tapes 3 {s.tapes 3 with head := (s.tapes 3).head + 1}}

theorem cleanup_step (storage : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 113) :
    PricedSteps ((program storage).next input tape) 1 s ((clearStart s).relocate 114) := by
  apply executeInstructions_sound (instructions := 1)
  simp [executeInstructions, BitRAM.next, program, hpc, TapeOps.copyClear,
    HornerMultiply.program, NormalizeWord.program, ScanForward.program, TapeOps.trim,
    Rewind.program, TapeOps.clear, BitRAMInstruction.relocate, RewindOvershoot.program,
    RewindOvershoot.preamble, BitRAM.link, rippleAdder,
    BitRAMState.setTape, BitRAMState.relocate, clearStart]

theorem frame_clearStart (storage : ℕ) (s : BitRAMState) : Frame storage s (clearStart s) := by
  simp [Frame, clearStart]
  intro i h4 _
  simp [show i ≠ 3 by omega]

/-- A stored nonnegative word is multiplied by the fixed nonempty
denominator word. The exact canonical result replaces the stored word;
all three integer scratch tapes are blank for the next update. -/
theorem simulation (storage : ℕ) (hstorage : 4 ≤ storage)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool)
    (ao xo zo yo storageOrigin : ℤ) (hxs : 0 < xs.length)
    (s : BitRAMState) (hpc : s.pc = 0)
    (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = {BitTape.blank with head := yo})
    (hword : s.tapes storage = BitTape.shifted ys storageOrigin) :
    ∃ cost t resultOrigin scratchOrigin,
      cost ≤ 500 * (xs.length + ys.length + 2) ^ 2 ∧
      PricedSteps ((program storage).next input tape) cost s t ∧ t.pc = 120 ∧
      t.tapes storage = BitTape.shifted (addressValue xs * addressValue ys).bits
        (storageOrigin + ys.length) ∧
      t.tapes 0 = {BitTape.blank with head := resultOrigin} ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 3 = {BitTape.blank with head := yo + ys.length} ∧ Frame storage s t := by
  obtain ⟨copied, hcopy, hcopyPc, hcopyStorage, hcopy3, hcopyFrame⟩ :=
    TapeOps.copyClear_to_blank_steps storage 3 (by omega) input tape ys storageOrigin yo
      {s with pc := 0} rfl hword h3
  let s1 : BitRAMState := {copied with pc := 8}
  have hs1 := (contains_input storage).call_at input tape s copied hpc hcopy
    (by simp [TapeOps.copyClear, hcopyPc])
  have hc0 : s1.tapes 0 = {BitTape.blank with head := ao} :=
    (hcopyFrame.2.2.2.2.2.1 0 (by omega) (by omega)).trans h0
  have hc1 : s1.tapes 1 = BitTape.shifted xs xo :=
    (hcopyFrame.2.2.2.2.2.1 1 (by omega) (by omega)).trans h1
  have hc2 : s1.tapes 2 = {BitTape.blank with head := zo} :=
    (hcopyFrame.2.2.2.2.2.1 2 (by omega) (by omega)).trans h2
  obtain ⟨mulCost, multiplied, raw, ro, so, hmCost, hm, hmPc, hm0, hm1, hm2, hmValue,
      hmLength, hm3⟩ := HornerMultiply.simulation_nonempty_cleanup input tape
        {s1 with pc := 0} xs ys ao xo zo yo hxs rfl hc0 hc1 hc2 hcopy3
  let s2 : BitRAMState := {multiplied with pc := 80}
  have hs2 := (contains_multiply storage).call_at input tape s1 multiplied rfl hm
    (by simp [HornerMultiply.program, hmPc, RewindOvershoot.program, Rewind.program,
      RewindOvershoot.preamble, BitRAM.link, rippleAdder, TapeOps.clear,
      TapeOps.copyClear, BitRAMInstruction.relocate])
  have hmFrame := HornerMultiply.execution_frame input tape hm
  have hmStorage : s2.tapes storage =
      {BitTape.blank with head := storageOrigin + ys.length} :=
    (hmFrame.2.2.2.2.2.1 storage hstorage).trans hcopyStorage
  obtain ⟨normCost, normalized, hnCost, hn, hnPc, hn0, hnLength, hnFrame⟩ :=
    NormalizeWord.simulation 0 ro input tape raw {s2 with pc := 0} rfl hm0
  let s3 : BitRAMState := {normalized with pc := 100}
  have hs3 := (contains_normalize storage).call_at input tape s2 normalized rfl hn
    (by simp [NormalizeWord.program, hnPc, ScanForward.program, TapeOps.trim,
      Rewind.program, BitRAMInstruction.relocate])
  have hnStorage : s3.tapes storage =
      {BitTape.blank with head := storageOrigin + ys.length} :=
    (hnFrame.2.2.2.2.2.1 storage (by omega)).trans hmStorage
  let canonical := (addressValue raw).bits
  obtain ⟨stored, hstore, hstorePc, hstore0, hstoreWord, hstoreFrame⟩ :=
    TapeOps.copyClear_to_blank_steps 0 storage (by omega) input tape canonical ro
      (storageOrigin + ys.length) {s3 with pc := 0} rfl hn0 hnStorage
  let s4 : BitRAMState := {stored with pc := 108}
  have hs4 := (contains_output storage).call_at input tape s3 stored rfl hstore
    (by simp [TapeOps.copyClear, hstorePc])
  have hr := Rewind.stepsAt storage (storageOrigin + ys.length) input tape canonical.length
    {s4 with pc := 0} rfl
    (by simp [s4, hstoreWord, BitTape.shiftedEnd])
    (by simp [s4, hstoreWord, BitTape.shiftedEnd, BitTape.shifted])
    (by
      intro k hk
      refine ⟨canonical[k], ?_⟩
      simp [s4, hstoreWord, BitTape.shiftedEnd, BitTape.shifted, hk])
  let rewound := Rewind.finishAt storage (storageOrigin + ys.length) {s4 with pc := 0}
  let s5 : BitRAMState := {rewound with pc := 113}
  have hs5 := (contains_rewind storage).call_at input tape s4 rewound rfl hr
    (by simp [rewound, Rewind.program, Rewind.finishAt])
  have hn3 : s3.tapes 3 = {BitTape.shifted ys yo with head := yo - 1} :=
    (hnFrame.2.2.2.2.2.1 3 (by omega)).trans hm3
  have hstore3 : s4.tapes 3 = {BitTape.shifted ys yo with head := yo - 1} :=
    (hstoreFrame.2.2.2.2.2.1 3 (by omega) (by omega)).trans hn3
  have hr3 : s5.tapes 3 = {BitTape.shifted ys yo with head := yo - 1} := by
    simpa [s5, rewound, Rewind.finishAt, show 3 ≠ storage by omega] using hstore3
  have hmove := cleanup_step storage input tape s5 rfl
  have hready3 : (clearStart s5).tapes 3 = BitTape.shifted ys yo := by
    simp [clearStart, hr3, BitTape.shifted]
  obtain ⟨cleared, hclear, hclearPc, hclear3, hclearFrame⟩ :=
    TapeOps.clear_steps 3 input tape ys yo (clearStart s5) rfl hready3
  have hclear' := (contains_clear storage).call input tape hclear
    (by simp [TapeOps.clear, hclearPc])
  let finalState : BitRAMState := {cleared with pc := 120}
  have hFcopy : Frame storage s s1 := frame_of_copy (Or.inl rfl) (Or.inr (by omega)) hcopyFrame
  have hFmul : Frame storage s1 s2 := frame_of_multiply hmFrame
  have hFnorm : Frame storage s2 s3 := frame_of_normalize hnFrame
  have hFstore : Frame storage s3 s4 := frame_of_copy (Or.inr (by omega)) (Or.inl rfl) hstoreFrame
  have hFrewind : Frame storage s4 s5 := frame_rewind storage (storageOrigin + ys.length) {s4 with pc := 0}
  have hFmove : Frame storage s5 (clearStart s5) := frame_clearStart storage s5
  have hFclear : Frame storage (clearStart s5) finalState :=
    frame_of_copy (Or.inr (by omega)) (Or.inr (by omega)) hclearFrame
  refine ⟨(8 * ys.length + 3 + 1) + (mulCost + 1) + (normCost + 1) +
      (8 * canonical.length + 3 + 1) + (4 * canonical.length + 5 + 1) + 1 +
      (6 * ys.length + 3 + 1), finalState, ro + canonical.length, so, ?_,
    ((((((hs1.trans hs2).trans hs3).trans hs4).trans hs5).trans hmove).trans hclear'), rfl,
    ?_, ?_, ?_, ?_, hclear3,
    (((((hFcopy.trans hFmul).trans hFnorm).trans hFstore).trans hFrewind).trans hFmove).trans hFclear⟩
  · dsimp [canonical]
    have hprod : (xs.length + ys.length + 2) * (ys.length + 1) ≤
        (xs.length + ys.length + 2) ^ 2 := by nlinarith
    have hlinear : 28 * xs.length + 70 * ys.length + 38 ≤
        100 * (xs.length + ys.length + 2) ^ 2 := by nlinarith
    nlinarith
  · have hrewound : s5.tapes storage = BitTape.shifted canonical (storageOrigin + ys.length) := by
      simp [s5, rewound, Rewind.finishAt, s4, hstoreWord, BitTape.shiftedEnd, BitTape.shifted]
    have hclean := hclearFrame.2.2.2.2.2.1 storage (by omega) (by omega)
    have hout : finalState.tapes storage = BitTape.shifted canonical (storageOrigin + ys.length) := by
      simpa [finalState, clearStart, show storage ≠ 3 by omega] using hclean.trans
        (by simpa [clearStart, show storage ≠ 3 by omega] using hrewound)
    simpa [canonical, hmValue] using hout
  · have hrewound0 : s5.tapes 0 = {BitTape.blank with head := ro + canonical.length} := by
      simpa [s5, rewound, Rewind.finishAt, show 0 ≠ storage by omega] using hstore0
    have hclean := hclearFrame.2.2.2.2.2.1 0 (by omega) (by omega)
    simpa [finalState, clearStart] using hclean.trans (by simpa [clearStart] using hrewound0)
  · have hn1 : s3.tapes 1 = BitTape.shifted xs xo :=
      (hnFrame.2.2.2.2.2.1 1 (by omega)).trans hm1
    have hstore1 : s4.tapes 1 = BitTape.shifted xs xo :=
      (hstoreFrame.2.2.2.2.2.1 1 (by omega) (by omega)).trans hn1
    have hrewound1 : s5.tapes 1 = BitTape.shifted xs xo := by
      simpa [s5, rewound, Rewind.finishAt, show 1 ≠ storage by omega] using hstore1
    have hclean := hclearFrame.2.2.2.2.2.1 1 (by omega) (by omega)
    simpa [finalState, clearStart] using hclean.trans (by simpa [clearStart] using hrewound1)
  · have hn2 : s3.tapes 2 = {BitTape.blank with head := so} :=
      (hnFrame.2.2.2.2.2.1 2 (by omega)).trans hm2
    have hstore2 : s4.tapes 2 = {BitTape.blank with head := so} :=
      (hstoreFrame.2.2.2.2.2.1 2 (by omega) (by omega)).trans hn2
    have hrewound2 : s5.tapes 2 = {BitTape.blank with head := so} := by
      simpa [s5, rewound, Rewind.finishAt, show 2 ≠ storage by omega] using hstore2
    have hclean := hclearFrame.2.2.2.2.2.1 2 (by omega) (by omega)
    simpa [finalState, clearStart] using hclean.trans (by simpa [clearStart] using hrewound2)

/-- The interpreter cap is uniform in the stored values and in the random tape. -/
theorem run (storage : ℕ) (hstorage : 4 ≤ storage)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool)
    (ao xo zo yo storageOrigin : ℤ) (hxs : 0 < xs.length)
    (s : BitRAMState) (hpc : s.pc = 0)
    (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = {BitTape.blank with head := yo})
    (hword : s.tapes storage = BitTape.shifted ys storageOrigin) :
    ∃ t resultOrigin scratchOrigin,
      (runPriced ((program storage).next input tape)
        (500 * (xs.length + ys.length + 2) ^ 2 + 1) s).finished = some t ∧
      (runPriced ((program storage).next input tape)
        (500 * (xs.length + ys.length + 2) ^ 2 + 1) s).instructions ≤
          500 * (xs.length + ys.length + 2) ^ 2 ∧
      t.tapes storage = BitTape.shifted (addressValue xs * addressValue ys).bits
        (storageOrigin + ys.length) ∧
      t.tapes 0 = {BitTape.blank with head := resultOrigin} ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 3 = {BitTape.blank with head := yo + ys.length} ∧ Frame storage s t := by
  obtain ⟨cost, t, ro, so, hc, hs, hp, hw, hzero, hone, htwo, hthree, hf⟩ :=
    simulation storage hstorage input tape xs ys ao xo zo yo storageOrigin hxs s hpc
      h0 h1 h2 h3 hword
  have halt : (program storage).next input tape t = none := by
    simp [BitRAM.next, program, hp, TapeOps.copyClear, HornerMultiply.program,
      NormalizeWord.program, ScanForward.program, TapeOps.trim, Rewind.program,
      TapeOps.clear, BitRAMInstruction.relocate, RewindOvershoot.program,
      RewindOvershoot.preamble, BitRAM.link, rippleAdder]
  have hr := hs.runPriced_ge halt (500 * (xs.length + ys.length + 2) ^ 2 + 1) (by omega)
  exact ⟨t, ro, so, hr.1, hr.2 ▸ hc, hw, hzero, hone, htwo, hthree, hf⟩

end Maxwell.Cost.StoredProduct
