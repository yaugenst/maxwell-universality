import Maxwell.Cost.LogRats

/-! Count-prefixed rational-list parsing, with the count physically read
from the input and every exact rational retained on tape 20. -/

namespace Maxwell.Cost.ParseRats

def program : BitRAM := ⟨
  (ParseNat.programOn 21).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10] ++
  (Rewind.program 21).code.map (BitRAMInstruction.relocate 20 25) ++
  LogRats.program.code.map (BitRAMInstruction.relocate 25 162) ++ [.halt]⟩

theorem header_contains : program.Contains (ParseNat.programOn 21) 0 19 := by decide
theorem rewind_contains : program.Contains (Rewind.program 21) 20 25 := by decide
set_option maxRecDepth 4096 in
theorem loop_contains : program.Contains LogRats.program 25 162 := by decide
theorem halt_instruction : program.code[162]? = some .halt := by decide

def price (values : List ℚ) : ℕ :=
  21 * values.length.bits.length + 16 + LogRats.price values.length.bits values

def resetState (s : BitRAMState) : BitRAMState :=
  {s with pc := 0, tapes := Function.update s.tapes 10 BitTape.blank}

def loopStart (s : BitRAMState) : BitRAMState :=
  {Rewind.finish 21 (resetState s) with pc := 0}

theorem reset_block (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState)
    (hcount : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input tape) 1 {s with pc := 19} ((resetState s).relocate 20) := by
  apply executeInstructions_sound (instructions := 1)
  have h19 : program.code[19]? = some (.tapeRight 10) := by decide
  simp [executeInstructions, BitRAM.next, h19, BitRAMState.setTape, BitRAMState.relocate,
    resetState, hcount, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

set_option maxRecDepth 4096 in
theorem steps (values : List ℚ) (preceding suffix archive : List Bool)
    (tape : ℕ → Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hready : LogRat.Ready initial)
    (hcounter : initial.tapes 21 = BitTape.blank)
    (hlog : initial.tapes 20 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      PricedSteps (program.next (preceding ++ (Codec.list Codec.rat values ++ suffix)) tape)
        (price values) initial final ∧
      final.pc = 162 ∧
      final.inputHead = initial.inputHead + (Codec.list Codec.rat values).length ∧
      final.tapes 20 = BitTape.atEnd (archive ++ LogRats.records values) ∧
      LogRat.Ready final ∧ LogRats.Frame 21 initial final := by
  let input := preceding ++ (Codec.list Codec.rat values ++ suffix)
  obtain ⟨s, hs, hspc, hshead, hscount, hsout, hframe⟩ :=
    ParseNat.parse_on_steps 21 (by decide) values.length preceding (LogRats.records values ++ suffix)
      tape initial hpc hhead hready.1 hcounter
  have hi : preceding ++ (Codec.nat values.length ++ (LogRats.records values ++ suffix)) = input := by
    simp [input, Codec.list, LogRats.records, List.append_assoc]
  rw [hi] at hs
  have hp := header_contains.call input tape hs (by
    simp [ParseNat.programOn, BitRAM.renameTapes, ParseNat.program, hspc,
      BitRAMInstruction.renameTapes])
  simp only [BitRAMState.relocate_zero] at hp
  have hrword : (resetState s).tapes 21 = BitTape.atEnd values.length.bits := by
    simpa [resetState] using hsout
  have hr := rewind_contains.call input tape
    (Rewind.atEnd_steps 21 input tape values.length.bits (resetState s) rfl hrword)
    (by simp [Rewind.program, Rewind.finish])
  have hlword : (loopStart s).tapes 21 = BitTape.ofList values.length.bits :=
    Rewind.finish_tape 21 values.length.bits (resetState s) hrword
  have hlhead : (loopStart s).inputHead = (preceding ++ Codec.nat values.length).length := by
    simpa [loopStart, Rewind.finish, resetState, hhead] using hshead
  have hlother (i : ℕ) (hi10 : i ≠ 10) (hi21 : i ≠ 21) :
      (loopStart s).tapes i = initial.tapes i := by
    simpa [loopStart, Rewind.finish, resetState, hi10, hi21] using hframe.2.2.2.2.1 i hi10 hi21
  have hlready : LogRat.Ready (loopStart s) := by
    refine ⟨?_, (hlother 12 (by decide) (by decide)).trans hready.2.1,
      (hlother 13 (by decide) (by decide)).trans hready.2.2⟩
    simp [loopStart, Rewind.finish, resetState]
  have hllog : (loopStart s).tapes 20 = BitTape.atEnd archive :=
    (hlother 20 (by decide) (by decide)).trans hlog
  obtain ⟨t, ht, htpc, hthead, htlog, htready, htframe⟩ :=
    LogRats.steps values values.length.bits (preceding ++ Codec.nat values.length) suffix archive
      tape (loopStart s) rfl hlhead (addressValue_bits values.length) hlword hlready hllog
  have hli : (preceding ++ Codec.nat values.length) ++ (LogRats.records values ++ suffix) = input := by
    simp [input, Codec.list, LogRats.records, List.append_assoc]
  rw [hli] at ht
  have hl := loop_contains.call input tape ht (by
    have hp' : t.pc = 136 := htpc
    simpa [hp'] using LogRats.halt_instruction)
  refine ⟨{t with pc := 162}, ?_, rfl, ?_, htlog, htready, ?_⟩
  · change PricedSteps (program.next input tape) _ initial _
    convert ((hp.trans (reset_block input tape s hscount)).trans hr).trans hl using 1
    dsimp [price]
    omega
  · simp only [loopStart, Rewind.finish, resetState] at hthead
    simp only [Codec.list, List.length_append]
    dsimp only [LogRats.records] at hthead
    omega
  · refine ⟨htframe.1.trans hframe.1, htframe.2.1.trans hframe.2.1,
      htframe.2.2.1.trans hframe.2.2.1, htframe.2.2.2.1.trans hframe.2.2.2.1, ?_⟩
    intro i h10 h12 h13 h21 h20
    exact (htframe.2.2.2.2 i h10 h12 h13 h21 h20).trans (hlother i h10 h21)

theorem run (values : List ℚ) (preceding suffix archive : List Bool)
    (tape : ℕ → Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length) (hready : LogRat.Ready initial)
    (hcounter : initial.tapes 21 = BitTape.blank)
    (hlog : initial.tapes 20 = BitTape.atEnd archive) :
    ∃ final : BitRAMState,
      (runPriced (program.next (preceding ++ (Codec.list Codec.rat values ++ suffix)) tape)
        (price values + 1) initial).finished = some final ∧
      (runPriced (program.next (preceding ++ (Codec.list Codec.rat values ++ suffix)) tape)
        (price values + 1) initial).instructions = price values ∧
      final.inputHead = initial.inputHead + (Codec.list Codec.rat values).length ∧
      final.tapes 20 = BitTape.atEnd (archive ++ LogRats.records values) ∧
      LogRat.Ready final ∧ LogRats.Frame 21 initial final := by
  obtain ⟨final, hf, hfpc, hh, hl, hr, hframe⟩ :=
    steps values preceding suffix archive tape initial hpc hhead hready hcounter hlog
  obtain ⟨hfinished, hcost⟩ := hf.runPriced (by simp [BitRAM.next, hfpc, halt_instruction])
  exact ⟨final, hfinished, hcost, hh, hl, hr, hframe⟩

theorem price_le (values : List ℚ) :
    price values ≤ 21 * values.length.bits.length + 16 +
      (values.length + 1) * (13 * values.length.bits.length + 13) +
      29 * (LogRats.records values).length := by
  have h := LogRats.price_le values.length.bits values
  dsimp [price]
  omega

end Maxwell.Cost.ParseRats
