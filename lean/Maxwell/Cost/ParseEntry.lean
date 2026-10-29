import Maxwell.Cost.ParseRat
import Maxwell.Cost.Blocks
import Maxwell.Codec.Source

/-! A fixed program parses every stored sparse matrix entry into its two
indices and exact signed rational fields. -/

namespace Maxwell.Cost
namespace ParseNat

def programOn (outputTape : ℕ) : BitRAM := program.renameTapes (Equiv.swap 11 outputTape)

def FrameAt (outputTape : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ outputTape → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 20 → i ≠ 21 → i ≠ 22 → t.registers i = s.registers i)

theorem parse_on_steps (outputTape : ℕ) (hne : outputTape ≠ 10)
    (n : ℕ) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (initial : BitRAMState) (hipc : initial.pc = 0)
    (hihead : initial.inputHead = preceding.length)
    (hicount : initial.tapes 10 = BitTape.blank)
    (hiout : initial.tapes outputTape = BitTape.blank) :
    ∃ t : BitRAMState,
      PricedSteps ((programOn outputTape).next (preceding ++ (Codec.nat n ++ suffix)) randomTape)
        (17 * n.bits.length + 7) initial t ∧
      t.pc = 18 ∧ t.inputHead = initial.inputHead + (Codec.nat n).length ∧
      t.tapes 10 = BitTape.beforeEnd [] ∧ t.tapes outputTape = BitTape.atEnd n.bits ∧
      FrameAt outputTape initial t := by
  let p : Equiv.Perm ℕ := Equiv.swap 11 outputTape
  obtain ⟨s, hs, hspc, hshead, hscount, hsout, hframe⟩ :=
    parse_nat_steps n preceding suffix randomTape (initial.renameTapes p.symm) hipc hihead
      (by simpa [BitRAMState.renameTapes, p, Equiv.swap_apply_def, Ne.symm hne] using hicount)
      (by simpa [BitRAMState.renameTapes, p] using hiout)
  have hrenamed := hs.renameTapes p
  rw [BitRAMState.renameTapes_inverse] at hrenamed
  refine ⟨s.renameTapes p, hrenamed, hspc, hshead, ?_, ?_, ?_⟩
  · simpa [BitRAMState.renameTapes, p, Equiv.swap_apply_def, Ne.symm hne] using hscount
  · simpa [BitRAMState.renameTapes, p] using hsout
  · rcases hframe with ⟨ha, hm, hr, ho, ht, hg⟩
    refine ⟨ha, hm, hr, ho, ?_, hg⟩
    intro i h10 hout
    have hp10 : p.symm i ≠ 10 := by
      intro heq
      have hh : i = p 10 := by simpa only [Equiv.apply_symm_apply] using congrArg p heq
      apply h10
      simpa [p, Equiv.swap_apply_def, Ne.symm hne] using hh
    have hp11 : p.symm i ≠ 11 := by
      intro heq
      have hh := congrArg p heq
      simp [p] at hh
      exact hout hh
    simpa [BitRAMState.renameTapes, Function.comp_def] using ht (p.symm i) hp10 hp11

end ParseNat

namespace ParseEntry

def encode (row column : ℕ) (value : ℚ) : List Bool :=
  Codec.nat row ++ Codec.nat column ++ Codec.rat value

theorem encode_source_entry (S : Source.SparseSystem)
    (p : {p // p ∈ Codec.sourceEntries S}) :
    encode p.val.1.val p.val.2.val
      (S.matrix.coefficient ⟨p.val, (Codec.mem_sourceEntries S p.val).mp p.property⟩) =
        Codec.sourceEntry S p := rfl

theorem wire_roundtrip (row column : ℕ) (value : ℚ) (suffix : List Bool) :
    Codec.readSourceEntry (encode row column value ++ suffix) = some ((row, column, value), suffix) := by
  simp [Codec.readSourceEntry, encode, List.append_assoc,
    Codec.readNat_append, Codec.readRat_append]

def program : BitRAM := ⟨
  (ParseNat.programOn 15).code.map (BitRAMInstruction.relocate 0 19) ++ [.tapeRight 10] ++
  (ParseNat.programOn 16).code.map (BitRAMInstruction.relocate 20 39) ++ [.tapeRight 10] ++
  ParseRat.program.code.map (BitRAMInstruction.relocate 40 83) ++ [.halt]⟩

theorem row_contains : program.Contains (ParseNat.programOn 15) 0 19 := by decide
theorem column_contains : program.Contains (ParseNat.programOn 16) 20 39 := by decide
theorem rational_contains : program.Contains ParseRat.program 40 83 := by decide

def resetState (pc : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with pc := pc, tapes := Function.update s.tapes 10 BitTape.blank}

theorem reset_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (pc : ℕ) (hc : program.code[pc]? = some (.tapeRight 10))
    (ht : s.tapes 10 = BitTape.beforeEnd []) :
    PricedSteps (program.next input randomTape) 1 {s with pc := pc} (resetState (pc + 1) s) := by
  apply executeInstructions_sound (instructions := 1)
  simp [executeInstructions, BitRAM.next, hc, ht, BitRAMState.setTape,
    resetState, BitTape.beforeEnd, BitTape.ofList, BitTape.blank]

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 15 → i ≠ 16 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 20 → i ≠ 21 → i ≠ 22 → i ≠ 23 → t.registers i = s.registers i)

theorem steps (row column : ℕ) (value : ℚ) (preceding suffix : List Bool)
    (randomTape : ℕ → Bool) (initial : BitRAMState) (hpc : initial.pc = 0)
    (hhead : initial.inputHead = preceding.length)
    (hcount : initial.tapes 10 = BitTape.blank)
    (hrow : initial.tapes 15 = BitTape.blank) (hcolumn : initial.tapes 16 = BitTape.blank)
    (hnum : initial.tapes 12 = BitTape.blank) (hden : initial.tapes 13 = BitTape.blank) :
    ∃ final : BitRAMState,
      PricedSteps (program.next (preceding ++ (encode row column value ++ suffix)) randomTape)
        (17 * (row.bits.length + column.bits.length + value.num.natAbs.bits.length +
          value.den.bits.length) + 39) initial final ∧
      final.pc = 83 ∧ final.inputHead = initial.inputHead + (encode row column value).length ∧
      final.tapes 10 = BitTape.beforeEnd [] ∧
      final.tapes 15 = BitTape.atEnd row.bits ∧ final.tapes 16 = BitTape.atEnd column.bits ∧
      final.tapes 12 = BitTape.atEnd value.num.natAbs.bits ∧
      final.tapes 13 = BitTape.atEnd value.den.bits ∧
      final.registers 23 = decide (value.num < 0) ∧ Frame initial final := by
  let input := preceding ++ (encode row column value ++ suffix)
  obtain ⟨r, hr, hrpc, hrhead, hrcount, hrout, hrframe⟩ :=
    ParseNat.parse_on_steps 15 (by decide) row preceding
      (Codec.nat column ++ (Codec.rat value ++ suffix)) randomTape initial hpc hhead hcount hrow
  have hri : preceding ++ (Codec.nat row ++ (Codec.nat column ++ (Codec.rat value ++ suffix))) = input := by
    simp [input, encode, List.append_assoc]
  rw [hri] at hr
  have hrCall := row_contains.call input randomTape hr (by
    simp [ParseNat.programOn, BitRAM.renameTapes, ParseNat.program, hrpc, BitRAMInstruction.renameTapes])
  simp only [BitRAMState.relocate_zero] at hrCall
  have hrReset := reset_block input randomTape r 19 (by decide) hrcount
  let colStart := {resetState 20 r with pc := 0}
  have hcolHead : colStart.inputHead = (preceding ++ Codec.nat row).length := by
    simpa [colStart, resetState, hhead] using hrhead
  have hcolTape : colStart.tapes 16 = BitTape.blank := by
    have ht := hrframe.2.2.2.2.1 16 (by decide) (by decide)
    simpa [colStart, resetState, hcolumn] using ht
  obtain ⟨c, hc, hcpc, hchead, hccount, hcout, hcframe⟩ :=
    ParseNat.parse_on_steps 16 (by decide) column (preceding ++ Codec.nat row)
      (Codec.rat value ++ suffix) randomTape colStart rfl hcolHead
      (by simp [colStart, resetState]) hcolTape
  have hci : (preceding ++ Codec.nat row) ++ (Codec.nat column ++ (Codec.rat value ++ suffix)) = input := by
    simp [input, encode, List.append_assoc]
  rw [hci] at hc
  have hcCall := column_contains.call input randomTape hc (by
    simp [ParseNat.programOn, BitRAM.renameTapes, ParseNat.program, hcpc, BitRAMInstruction.renameTapes])
  have hcStart : colStart.relocate 20 = resetState 20 r := by
    simp [colStart, resetState, BitRAMState.relocate]
  rw [hcStart] at hcCall
  have hcReset := reset_block input randomTape c 39 (by decide) hccount
  let ratStart := {resetState 40 c with pc := 0}
  have hratHead : ratStart.inputHead = (preceding ++ (Codec.nat row ++ Codec.nat column)).length := by
    simp only [colStart, resetState] at hchead
    simp only [ratStart, resetState, List.length_append, Nat.cast_add]
    simp only [hhead] at hrhead
    omega
  have hratTape (i : ℕ) (hi10 : i ≠ 10) (hi15 : i ≠ 15) (hi16 : i ≠ 16) :
      ratStart.tapes i = initial.tapes i := by
      have ht := (hcframe.2.2.2.2.1 i hi10 hi16)
      have ht' := hrframe.2.2.2.2.1 i hi10 hi15
      simp only [colStart, resetState, Function.update_of_ne hi10] at ht
      simpa [ratStart, colStart, resetState, Function.update_of_ne hi10] using ht.trans ht'
  obtain ⟨q, hq, hqpc, hqhead, hqcount, hqnum, hqden, hqsign, hqframe⟩ :=
    ParseRat.parse_rat_steps value (preceding ++ (Codec.nat row ++ Codec.nat column)) suffix
      randomTape ratStart rfl hratHead (by simp [ratStart, resetState])
      ((hratTape 12 (by decide) (by decide) (by decide)).trans hnum)
      ((hratTape 13 (by decide) (by decide) (by decide)).trans hden)
  have hqi : (preceding ++ (Codec.nat row ++ Codec.nat column)) ++ (Codec.rat value ++ suffix) = input := by
    simp [input, encode, List.append_assoc]
  rw [hqi] at hq
  have hqCall := rational_contains.call input randomTape hq (by
    have hh : ParseRat.program.code[42]? = some .halt := by decide
    simpa [hqpc] using hh)
  have hqStart : ratStart.relocate 40 = resetState 40 c := by
    simp [ratStart, resetState, BitRAMState.relocate]
  rw [hqStart] at hqCall
  have hall : PricedSteps (program.next input randomTape)
      (17 * (row.bits.length + column.bits.length + value.num.natAbs.bits.length +
        value.den.bits.length) + 39) initial {q with pc := 83} := by
    convert (((hrCall.trans hrReset).trans hcCall).trans hcReset).trans hqCall using 1
    omega
  refine ⟨{q with pc := 83}, hall, rfl, ?_, hqcount, ?_, ?_, hqnum, hqden, hqsign, ?_⟩
  · simp only [ratStart, colStart, resetState] at hqhead hchead
    simp only [encode, List.length_append, Nat.cast_add]
    omega
  · have hqrow := hqframe.2.2.2.2.1 15 (by decide) (by decide) (by decide)
    have hcrow := hcframe.2.2.2.2.1 15 (by decide) (by decide)
    simpa [ratStart, colStart, resetState, hrout] using hqrow.trans hcrow
  · have hqcol := hqframe.2.2.2.2.1 16 (by decide) (by decide) (by decide)
    simpa [ratStart, resetState, hcout] using hqcol
  · rcases hrframe with ⟨hra, hrm, hrr, hro, hrt, hrg⟩
    rcases hcframe with ⟨hca, hcm, hcr, hco, hct, hcg⟩
    rcases hqframe with ⟨hqa, hqm, hqr, hqo, hqt, hqg⟩
    refine ⟨(hqa.trans hca).trans hra, (hqm.trans hcm).trans hrm,
      (hqr.trans hcr).trans hrr, (hqo.trans hco).trans hro, ?_, ?_⟩
    · intro i h10 h12 h13 h15 h16
      have hqr := hqt i h10 h12 h13
      have hcr := hct i h10 h16
      have hrr := hrt i h10 h15
      simp only [ratStart, colStart, resetState, Function.update_of_ne h10] at hqr hcr
      simpa [ratStart, colStart, resetState, Function.update_of_ne h10] using
        (hqr.trans hcr).trans hrr
    · intro i h20 h21 h22 h23
      exact ((hqg i h20 h21 h22 h23).trans (hcg i h20 h21 h22)).trans (hrg i h20 h21 h22)

theorem run (row column : ℕ) (value : ℚ) (suffix : List Bool) (randomTape : ℕ → Bool) :
    ∃ final : BitRAMState,
      (program.run (encode row column value ++ suffix) randomTape
        (17 * (row.bits.length + column.bits.length + value.num.natAbs.bits.length +
          value.den.bits.length) + 40)).finished = some final ∧
      (program.run (encode row column value ++ suffix) randomTape
        (17 * (row.bits.length + column.bits.length + value.num.natAbs.bits.length +
          value.den.bits.length) + 40)).instructions =
        17 * (row.bits.length + column.bits.length + value.num.natAbs.bits.length +
          value.den.bits.length) + 39 ∧
      final.inputHead = (encode row column value).length ∧
      final.tapes 15 = BitTape.atEnd row.bits ∧ final.tapes 16 = BitTape.atEnd column.bits ∧
      final.tapes 12 = BitTape.atEnd value.num.natAbs.bits ∧
      final.tapes 13 = BitTape.atEnd value.den.bits ∧ final.registers 23 = decide (value.num < 0) := by
  obtain ⟨final, hs, hp, hh, _, hr, hc, hn, hd, hsign, _⟩ :=
    steps row column value [] suffix randomTape BitRAMState.initial rfl rfl rfl rfl rfl rfl rfl
  have hhalt : program.next (encode row column value ++ suffix) randomTape final = none := by
    have hcode : program.code[83]? = some .halt := by decide
    simp [BitRAM.next, hp, hcode]
  obtain ⟨hfinish, hcost⟩ := hs.runPriced hhalt
  exact ⟨final, hfinish, hcost, by simpa [BitRAMState.initial] using hh, hr, hc, hn, hd, hsign⟩

end ParseEntry
end Maxwell.Cost
