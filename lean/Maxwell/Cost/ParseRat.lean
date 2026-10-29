import Maxwell.Cost.ParseNat
import Maxwell.Cost.Link

/-! Linked finite programs for the signed and rational wire codecs. -/

namespace Maxwell.Cost

theorem BitRAMState.renameTapes_inverse (p : Equiv.Perm ℕ) (s : BitRAMState) :
    (s.renameTapes p.symm).renameTapes p = s := by
  cases s
  simp [BitRAMState.renameTapes, Function.comp_def]

theorem BitRAMState.relocate_zero (s : BitRAMState) : s.relocate 0 = s := by
  cases s
  simp [BitRAMState.relocate]

namespace ParseInt

def preamble : List BitRAMInstruction := [.readSequential 23, .inputRight]

def program : BitRAM := BitRAM.link preamble ParseNat.program 21 [.halt]

def signedState (s : BitRAMState) (sign : Bool) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update s.registers 23 sign
    inputHead := s.inputHead + 1}

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 11 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 20 → i ≠ 21 → i ≠ 22 → i ≠ 23 → t.registers i = s.registers i)

theorem sign_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (sign : Bool) (hpc : s.pc = 0)
    (hb : inputBit input s.inputHead = sign) :
    PricedSteps (program.next input randomTape) 2 s ((signedState s sign).relocate 2) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, BitRAM.link, preamble, hpc, hb,
    BitRAMState.setRegister, signedState, BitRAMState.relocate]

/-- The sign read, natural payload invocation, and return jump are all
transitions of the same finite linked program. -/
theorem parse_int_steps (z : ℤ) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (initial : BitRAMState) (hipc : initial.pc = 0)
    (hihead : initial.inputHead = preceding.length)
    (hicount : initial.tapes 10 = BitTape.blank)
    (hiout : initial.tapes 11 = BitTape.blank) :
    ∃ t : BitRAMState,
      PricedSteps (program.next (preceding ++ (Codec.int z ++ suffix)) randomTape)
        (17 * z.natAbs.bits.length + 10) initial t ∧
      t.pc = 21 ∧ t.inputHead = initial.inputHead + (Codec.int z).length ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧ t.tapes 11 = BitTape.atEnd z.natAbs.bits ∧
      t.registers 23 = decide (z < 0) ∧ Frame initial t := by
  let sign := decide (z < 0)
  let input := preceding ++ (Codec.int z ++ suffix)
  let start := signedState initial sign
  have hsign : inputBit input initial.inputHead = sign := by
    rw [hihead]
    simpa [input, Codec.int, sign] using
      ParseNat.inputBit_append_offset preceding (Codec.int z ++ suffix) 0
  have hprefix : start.inputHead = (preceding ++ [sign]).length := by
    simp [start, signedState, hihead]
  obtain ⟨s, hnat, hpc, hhead, hcount, hout, hframe⟩ :=
    ParseNat.parse_nat_steps z.natAbs (preceding ++ [sign]) suffix randomTape
      start rfl hprefix hicount hiout
  have hinput : (preceding ++ [sign]) ++ (Codec.nat z.natAbs ++ suffix) = input := by
    simp [input, Codec.int, sign, List.append_assoc]
  rw [hinput] at hnat
  have hsignSteps := sign_block input randomTape initial sign hipc hsign
  have hlinked := hnat.link preamble 21 [.halt]
  have hreturn : PricedSteps (program.next input randomTape) 1
      (s.relocate 2) {s with pc := 21} := by
    exact PricedSteps.step
      (BitRAM.link_return preamble ParseNat.program 21 [.halt] input randomTape s
        (by simp [ParseNat.program, hpc])) (PricedSteps.refl _)
  have hall : PricedSteps (program.next input randomTape) (17 * z.natAbs.bits.length + 10)
      initial {s with pc := 21} := by
    convert (hsignSteps.trans hlinked).trans hreturn using 1
    omega
  refine ⟨{s with pc := 21}, hall, rfl, ?_, hcount, hout, ?_, ?_⟩
  · simp only [start, signedState] at hhead
    simpa [Codec.int, add_assoc, add_comm, add_left_comm] using hhead
  · have hh := hframe.2.2.2.2.2 23 (by decide) (by decide) (by decide)
    simpa [start, signedState] using hh
  · rcases hframe with ⟨ha, hm, hr, ho, ht, hg⟩
    refine ⟨ha, hm, hr, ho, ht, ?_⟩
    intro i h20 h21 h22 h23
    simpa [start, signedState, Function.update_of_ne h23] using hg i h20 h21 h22

theorem run_int (z : ℤ) (suffix : List Bool) (randomTape : ℕ → Bool) :
    ∃ t : BitRAMState,
      (program.run (Codec.int z ++ suffix) randomTape
        (17 * z.natAbs.bits.length + 11)).finished = some t ∧
      (program.run (Codec.int z ++ suffix) randomTape
        (17 * z.natAbs.bits.length + 11)).instructions = 17 * z.natAbs.bits.length + 10 ∧
      t.inputHead = (Codec.int z).length ∧
      t.tapes 11 = BitTape.atEnd z.natAbs.bits ∧ t.registers 23 = decide (z < 0) := by
  obtain ⟨t, hs, hp, hh, _, ho, hg, _⟩ :=
    parse_int_steps z [] suffix randomTape BitRAMState.initial rfl rfl rfl rfl
  have hhalt : program.next (Codec.int z ++ suffix) randomTape t = none := by
    simp [BitRAM.next, program, BitRAM.link, preamble, ParseNat.program, hp]
  obtain ⟨hf, hc⟩ := hs.runPriced hhalt
  exact ⟨t, hf, hc, by simpa [BitRAMState.initial] using hh, ho, hg⟩

end ParseInt

namespace ParseRat

attribute [local simp] Equiv.swap_apply_def

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 12 → i ≠ 13 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 20 → i ≠ 21 → i ≠ 22 → i ≠ 23 → t.registers i = s.registers i)

def numeratorProgram : BitRAM := ParseInt.program.renameTapes (Equiv.swap 11 12)

def denominatorProgram : BitRAM := ParseNat.program.renameTapes (Equiv.swap 11 13)

def denominatorPreamble : List BitRAMInstruction :=
  numeratorProgram.code.map (BitRAMInstruction.relocate 0 22) ++ [.tapeRight 10]

def numeratorSuffix : List BitRAMInstruction :=
  [.tapeRight 10] ++ denominatorProgram.code.map (BitRAMInstruction.relocate 23 42) ++ [.halt]

/-- Both numerical fields are parsed by the verified natural parser;
the intermediate head-reset and return jumps are explicit instructions. -/
def program : BitRAM := BitRAM.link [] numeratorProgram 22 numeratorSuffix

theorem denominatorPreamble_length : denominatorPreamble.length = 23 := by
  simp [denominatorPreamble, numeratorProgram, BitRAM.renameTapes, ParseInt.program,
    BitRAM.link, ParseInt.preamble, ParseNat.program]

theorem program_as_denominator :
    program = BitRAM.link denominatorPreamble denominatorProgram 42 [.halt] := by
  simp only [program, BitRAM.link, denominatorPreamble_length]
  simp [denominatorPreamble, numeratorSuffix, List.append_assoc]

def resetState (s : BitRAMState) : BitRAMState :=
  {s with pc := 23, tapes := Function.update s.tapes 10 BitTape.blank}

theorem reset_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (ht : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input randomTape) 1 {s with pc := 22} (resetState s) := by
  apply executeInstructions_sound (instructions := 1)
  simp [executeInstructions, program, BitRAM.next, BitRAM.link, numeratorProgram,
    BitRAM.renameTapes, ParseInt.program, ParseInt.preamble, ParseNat.program,
    numeratorSuffix, ht, BitRAMState.setTape, resetState,
    BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

theorem parse_rat_steps (q : ℚ) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (initial : BitRAMState) (hipc : initial.pc = 0)
    (hihead : initial.inputHead = preceding.length)
    (hicount : initial.tapes 10 = BitTape.blank)
    (hinum : initial.tapes 12 = BitTape.blank)
    (hiden : initial.tapes 13 = BitTape.blank) :
    ∃ t : BitRAMState,
      PricedSteps (program.next (preceding ++ (Codec.rat q ++ suffix)) randomTape)
        (17 * (q.num.natAbs.bits.length + q.den.bits.length) + 20) initial t ∧
      t.pc = 42 ∧ t.inputHead = initial.inputHead + (Codec.rat q).length ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧
      t.tapes 12 = BitTape.atEnd q.num.natAbs.bits ∧
      t.tapes 13 = BitTape.atEnd q.den.bits ∧ t.registers 23 = decide (q.num < 0) ∧
      Frame initial t := by
  let input := preceding ++ (Codec.rat q ++ suffix)
  let pnum : Equiv.Perm ℕ := Equiv.swap 11 12
  let pden : Equiv.Perm ℕ := Equiv.swap 11 13
  obtain ⟨ns, hn, hnpc, hnhead, hncount, hnout, hnsign, hnframe⟩ :=
    ParseInt.parse_int_steps q.num preceding (Codec.nat q.den ++ suffix) randomTape
      (initial.renameTapes pnum.symm) hipc hihead
      (by simpa [pnum, BitRAMState.renameTapes] using hicount)
      (by simpa [pnum, BitRAMState.renameTapes] using hinum)
  have hin : preceding ++ (Codec.int q.num ++ (Codec.nat q.den ++ suffix)) = input := by
    simp [input, Codec.rat, List.append_assoc]
  rw [hin] at hn
  let numerator := ns.renameTapes pnum
  have hnum : PricedSteps (numeratorProgram.next input randomTape)
      (17 * q.num.natAbs.bits.length + 10) initial numerator := by
    simpa only [BitRAMState.renameTapes_inverse, numeratorProgram, pnum, numerator] using
      hn.renameTapes pnum
  have hnumLinked := hnum.link [] 22 numeratorSuffix
  simp only [List.length_nil, BitRAMState.relocate_zero] at hnumLinked
  change PricedSteps (program.next input randomTape) _ initial numerator at hnumLinked
  have hnumReturn : PricedSteps (program.next input randomTape) 1
      numerator {numerator with pc := 22} := by
    simpa only [List.length_nil, BitRAMState.relocate_zero, program] using
      (PricedSteps.step (BitRAM.link_return [] numeratorProgram 22 numeratorSuffix input
        randomTape numerator (by
          simp [numerator, BitRAMState.renameTapes, numeratorProgram, BitRAM.renameTapes,
            ParseInt.program, BitRAM.link, ParseInt.preamble, ParseNat.program, hnpc,
            BitRAMInstruction.renameTapes])) (PricedSteps.refl _))
  have hnumCount : numerator.tapes 10 = BitTape.beforeEnd [] := by
    simpa [numerator, BitRAMState.renameTapes, pnum] using hncount
  have hnumOut : numerator.tapes 12 = BitTape.atEnd q.num.natAbs.bits := by
    simpa [numerator, BitRAMState.renameTapes, pnum] using hnout
  have hnumDen : numerator.tapes 13 = BitTape.blank := by
    have hh := hnframe.2.2.2.2.1 13 (by decide) (by decide)
    simpa [numerator, BitRAMState.renameTapes, pnum, hiden] using hh
  have hreset := reset_block input randomTape numerator hnumCount
  let denominatorStart := {resetState numerator with pc := 0}
  have hdhead : (denominatorStart.renameTapes pden.symm).inputHead =
      (preceding ++ Codec.int q.num).length := by
    simp only [BitRAMState.renameTapes, denominatorStart, resetState, numerator] at hnhead ⊢
    simp only [List.length_append, Nat.cast_add]
    simpa [hihead] using hnhead
  obtain ⟨ds, hd, hdpc, hdhead', hdcount, hdout, hdframe⟩ :=
    ParseNat.parse_nat_steps q.den (preceding ++ Codec.int q.num) suffix randomTape
      (denominatorStart.renameTapes pden.symm) rfl hdhead
      (by simp [denominatorStart, resetState, BitRAMState.renameTapes, pden])
      (by simpa [denominatorStart, resetState, BitRAMState.renameTapes, pden] using hnumDen)
  have hid : (preceding ++ Codec.int q.num) ++ (Codec.nat q.den ++ suffix) = input := by
    simp [input, Codec.rat, List.append_assoc]
  rw [hid] at hd
  let denominator := ds.renameTapes pden
  have hden : PricedSteps (denominatorProgram.next input randomTape)
      (17 * q.den.bits.length + 7) denominatorStart denominator := by
    simpa only [BitRAMState.renameTapes_inverse, denominatorProgram, pden, denominator] using
      hd.renameTapes pden
  have hdenLinked := hden.link denominatorPreamble 42 [.halt]
  rw [← program_as_denominator, denominatorPreamble_length] at hdenLinked
  have hstart : denominatorStart.relocate 23 = resetState numerator := by
    simp [denominatorStart, BitRAMState.relocate, resetState]
  rw [hstart] at hdenLinked
  have hdenReturn : PricedSteps (program.next input randomTape) 1
      (denominator.relocate 23) {denominator with pc := 42} := by
    rw [program_as_denominator]
    simpa only [denominatorPreamble_length] using
      (PricedSteps.step (BitRAM.link_return denominatorPreamble denominatorProgram 42 [.halt]
        input randomTape denominator (by
          simp [denominator, BitRAMState.renameTapes, denominatorProgram, BitRAM.renameTapes,
            ParseNat.program, hdpc, BitRAMInstruction.renameTapes])) (PricedSteps.refl _))
  have hall : PricedSteps (program.next input randomTape)
      (17 * (q.num.natAbs.bits.length + q.den.bits.length) + 20)
      initial {denominator with pc := 42} := by
    convert (((hnumLinked.trans hnumReturn).trans hreset).trans hdenLinked).trans hdenReturn using 1
    omega
  refine ⟨{denominator with pc := 42}, hall, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [BitRAMState.renameTapes, denominatorStart, resetState,
      numerator] at hdhead'
    simp only [BitRAMState.renameTapes] at hnhead
    simp only [denominator, BitRAMState.renameTapes, Codec.rat,
      List.length_append, Nat.cast_add]
    omega
  · simpa [denominator, BitRAMState.renameTapes, pden] using hdcount
  · have hh := hdframe.2.2.2.2.1 12 (by decide) (by decide)
    simpa [denominator, denominatorStart, resetState, BitRAMState.renameTapes, pden, hnumOut] using hh
  · simpa [denominator, BitRAMState.renameTapes, pden] using hdout
  · have hh := hdframe.2.2.2.2.2 23 (by decide) (by decide) (by decide)
    simpa [denominator, denominatorStart, resetState, numerator,
      BitRAMState.renameTapes, hnsign] using hh
  · rcases hnframe with ⟨hna, hnm, hnr, hno, hnt, hng⟩
    rcases hdframe with ⟨hda, hdm, hdr, hdo, hdt, hdg⟩
    refine ⟨hda.trans hna, hdm.trans hnm, hdr.trans hnr, hdo.trans hno, ?_, ?_⟩
    · intro i h10 h12 h13
      by_cases h11 : i = 11
      · subst i
        have hd' : ds.tapes 13 = ns.tapes 12 := by
          simpa [denominatorStart, resetState, numerator, BitRAMState.renameTapes,
            pden, pnum] using hdt 13 (by decide) (by decide)
        have hn' : ns.tapes 12 = initial.tapes 11 := by
          simpa [BitRAMState.renameTapes, pnum] using hnt 12 (by decide) (by decide)
        simpa [denominator, BitRAMState.renameTapes, pden] using hd'.trans hn'
      · have hd' : ds.tapes i = ns.tapes i := by
          simpa [denominatorStart, resetState, numerator, BitRAMState.renameTapes,
            pden, pnum, h10, h11, h12, h13] using hdt i h10 h11
        have hn' : ns.tapes i = initial.tapes i := by
          simpa [BitRAMState.renameTapes, pnum, h11, h12] using hnt i h10 h11
        simpa [denominator, BitRAMState.renameTapes, pden, h11, h13] using hd'.trans hn'
    · intro i h20 h21 h22 h23
      exact (hdg i h20 h21 h22).trans (hng i h20 h21 h22 h23)

theorem run_rat (q : ℚ) (suffix : List Bool) (randomTape : ℕ → Bool) :
    ∃ t : BitRAMState,
      (program.run (Codec.rat q ++ suffix) randomTape
        (17 * (q.num.natAbs.bits.length + q.den.bits.length) + 21)).finished = some t ∧
      (program.run (Codec.rat q ++ suffix) randomTape
        (17 * (q.num.natAbs.bits.length + q.den.bits.length) + 21)).instructions =
        17 * (q.num.natAbs.bits.length + q.den.bits.length) + 20 ∧
      t.inputHead = (Codec.rat q).length ∧
      t.tapes 12 = BitTape.atEnd q.num.natAbs.bits ∧
      t.tapes 13 = BitTape.atEnd q.den.bits ∧ t.registers 23 = decide (q.num < 0) := by
  obtain ⟨t, hs, hp, hh, _, hn, hd, hsign, _⟩ :=
    parse_rat_steps q [] suffix randomTape BitRAMState.initial rfl rfl rfl rfl rfl
  have hcode : program.code[42]? = some .halt := by decide
  have hhalt : program.next (Codec.rat q ++ suffix) randomTape t = none := by
    simp [BitRAM.next, hp, hcode]
  obtain ⟨hf, hc⟩ := hs.runPriced hhalt
  exact ⟨t, hf, hc, by simpa [BitRAMState.initial] using hh, hn, hd, hsign⟩

end ParseRat
end Maxwell.Cost
