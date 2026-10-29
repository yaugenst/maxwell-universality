import Maxwell.Cost.Blocks
import Maxwell.Cost.SourceGrouping.WordEq
import Maxwell.Cost.TapeReset
import Maxwell.Cost.Scan

namespace Maxwell.Cost.SourceGrouping.Boundary

/-- Fixed finite boundary-marker kernel. Tape 15 holds the current parsed
row, tape 22 the previous row, tape 24 the boundary stream. Register 33 says
whether a previous record exists. Both row words end at their zero origins. -/
def program : BitRAM := ⟨
  (Rewind.program 15).code.map (BitRAMInstruction.relocate 0 5) ++
  (Rewind.program 22).code.map (BitRAMInstruction.relocate 5 10) ++
  WordEq.program.code.map (BitRAMInstruction.relocate 10 26) ++
  (TapeReset.program 22).code.map (BitRAMInstruction.relocate 26 33) ++
  (Rewind.program 15).code.map (BitRAMInstruction.relocate 33 38) ++
  (Copy.program 15 22).code.map (BitRAMInstruction.relocate 38 45) ++
  [.bitAnd 34 31 33, .bitNot 34 34, .writeTape 24 34, .tapeRight 24,
    .literal 33 true, .halt]⟩

theorem first_contains : program.Contains (Rewind.program 15) 0 5 := by decide
theorem second_contains : program.Contains (Rewind.program 22) 5 10 := by decide
theorem compare_contains : program.Contains WordEq.program 10 26 := by decide
theorem clear_contains : program.Contains (TapeReset.program 22) 26 33 := by decide
theorem rewind_contains : program.Contains (Rewind.program 15) 33 38 := by decide
theorem copy_contains : program.Contains (Copy.program 15 22) 38 45 := by decide
theorem halt_instruction : program.code[50]? = some .halt := by decide

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  t.registers 23 = s.registers 23 ∧
  (∀ i, i ≠ 15 → i ≠ 22 → i ≠ 24 → t.tapes i = s.tapes i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]
theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, hg, ht⟩
  rcases k with ⟨ka, ki, km, kr, ko, kg, kt⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    kg.trans hg, fun i h15 h22 h24 => (kt i h15 h22 h24).trans (ht i h15 h22 h24)⟩

theorem Frame.pc (s : BitRAMState) (pc : ℕ) : Frame s {s with pc := pc} := by simp [Frame]

theorem Frame.rewind (s : BitRAMState) (workTape : ℕ) (h : workTape = 15 ∨ workTape = 22) :
    Frame s (Rewind.finish workTape s) := by
  rcases h with rfl | rfl <;> simp [Frame, Rewind.finish]
  all_goals intros; simp_all

theorem Frame.compare {s t : BitRAMState} (h : WordEq.frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2 23 (by decide),
    fun i h15 h22 _ => h.2.2.2.2.2.1 i h15 h22⟩

theorem Frame.clear (s : BitRAMState) : Frame s (TapeReset.finish 22 s) := by
  simp [Frame, TapeReset.finish]
  intros; simp_all

theorem Frame.copy {s t : BitRAMState} (h : TapeOps.Frame 15 22 s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.2 23 (by decide) (by decide),
    fun i h15 h22 _ => h.2.2.2.2.2.1 i h15 h22⟩

def finish (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 50
    registers := Function.update (Function.update s.registers 34
      (!(s.registers 31 && s.registers 33))) 33 true
    tapes := Function.update s.tapes 24
      {(s.tapes 24).write (some (!(s.registers 31 && s.registers 33))) with
        head := (s.tapes 24).head + 1}}

theorem finish_steps (input : List Bool) (tape : ℕ → Bool) (s : BitRAMState) (hpc : s.pc = 45) :
    PricedSteps (program.next input tape) 5 s (finish s) := by
  apply executeInstructions_sound (instructions := 5)
  have h45 : program.code[45]? = some (.bitAnd 34 31 33) := by decide
  have h46 : program.code[46]? = some (.bitNot 34 34) := by decide
  have h47 : program.code[47]? = some (.writeTape 24 34) := by decide
  have h48 : program.code[48]? = some (.tapeRight 24) := by decide
  have h49 : program.code[49]? = some (.literal 33 true) := by decide
  simp [executeInstructions, BitRAM.next, hpc, h45, h46, h47, h48, h49,
    BitRAMState.setRegister, BitRAMState.setTape, finish, BitTape.write]

theorem finish_frame (s : BitRAMState) : Frame s (finish s) := by
  simp [Frame, finish]
  intros; simp_all

/-- A boundary is emitted exactly when this is the first entry or its
actual row word differs from the preceding row word. All other parsed
fields are preserved for the existing canonical record logger. -/
theorem simulation (input : List Bool) (tape : ℕ → Bool) (row previous archive : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hrow : s.tapes 15 = BitTape.atEnd row)
    (hprevious : s.tapes 22 = BitTape.atEnd previous)
    (harchive : s.tapes 24 = BitTape.atEnd archive) :
    ∃ cost t, cost ≤ 30 * (row.length + previous.length + 2) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 50 ∧
      t.tapes 15 = BitTape.atEnd row ∧ t.tapes 22 = BitTape.atEnd row ∧
      t.tapes 24 = BitTape.atEnd (archive ++ [!((row == previous) && s.registers 33)]) ∧
      t.registers 33 = true ∧ Frame s t := by
  let a := {Rewind.finish 15 s with pc := 0}
  let b := {Rewind.finish 22 a with pc := 0}
  have ha := first_contains.call input tape (Rewind.atEnd_steps 15 input tape row s hpc hrow)
    (by simp [Rewind.program, Rewind.finish])
  have ha22 : a.tapes 22 = BitTape.atEnd previous := by simpa [a, Rewind.finish] using hprevious
  have hb := second_contains.call input tape (Rewind.atEnd_steps 22 input tape previous a rfl ha22)
    (by simp [Rewind.program, Rewind.finish])
  have hb15 : b.tapes 15 = BitTape.ofList row := by
    simpa [b, Rewind.finish, a] using Rewind.finish_tape 15 row s hrow
  have hb22 : b.tapes 22 = BitTape.ofList previous :=
    Rewind.finish_tape 22 previous a ha22
  obtain ⟨c, e, hc, he, hepc, heeq, he15, he22, hef⟩ :=
    WordEq.simulation input tape row previous b rfl hb15 hb22
  have he' := compare_contains.call input tape he (by simp [WordEq.program, hepc])
  let r := {TapeReset.finish 22 {e with pc := 0} with pc := 0}
  have hr := clear_contains.call input tape
    (TapeReset.steps 22 input tape previous {e with pc := 0} rfl he22)
    (by simp [TapeReset.program, TapeReset.finish])
  have hr15 : r.tapes 15 = BitTape.atEnd row := by simpa [r, TapeReset.finish] using he15
  let u := {Rewind.finish 15 r with pc := 0}
  have hu := rewind_contains.call input tape (Rewind.atEnd_steps 15 input tape row r rfl hr15)
    (by simp [Rewind.program, Rewind.finish])
  have hu15 : u.tapes 15 = BitTape.shifted row 0 := by
    simpa [BitTape.shifted, BitTape.ofList] using Rewind.finish_tape 15 row r hr15
  have hu22 : u.tapes 22 = {BitTape.blank with head := (0 : ℤ)} := by
    simp [u, r, Rewind.finish, TapeReset.finish, BitTape.blank]
  obtain ⟨v, hv, hvpc, hv15, hv22, hvf⟩ :=
    Copy.shifted_steps 15 22 (by decide) input tape row 0 0 u rfl hu15 hu22
  have hv' := copy_contains.call input tape hv (by simp [Copy.program, hvpc])
  let v' := {v with pc := 45}
  have hv33 : v'.registers 33 = s.registers 33 := by
    have h1 := hvf.2.2.2.2.2.2 33 (by decide) (by decide)
    have h2 := hef.2.2.2.2.2.2 33 (by decide)
    simpa [v', u, r, b, a, Rewind.finish, TapeReset.finish] using h1.trans h2
  have hv31 : v'.registers 31 = (row == previous) := by
    have h := hvf.2.2.2.2.2.2 31 (by decide) (by decide)
    simpa [v', u, r, Rewind.finish, TapeReset.finish] using h.trans heeq
  have hv24 : v'.tapes 24 = BitTape.atEnd archive := by
    have h1 := hvf.2.2.2.2.2.1 24 (by decide) (by decide)
    have h2 := hef.2.2.2.2.2.1 24 (by decide) (by decide)
    simpa [v', u, r, b, a, Rewind.finish, TapeReset.finish] using (h1.trans h2).trans harchive
  refine ⟨15 * row.length + 10 * previous.length + c + 34, finish v', ?_, ?_, rfl,
    ?_, ?_, ?_, by simp [finish], ?_⟩
  · omega
  · convert (((((ha.trans hb).trans he').trans hr).trans hu).trans hv').trans
      (finish_steps input tape v' rfl) using 1
    · omega
    · cases s
      simp_all [BitRAMState.relocate]
  · simpa [finish, v', BitTape.shiftedEnd, BitTape.shifted, BitTape.atEnd, BitTape.ofList] using hv15
  · simpa [finish, v', BitTape.shiftedEnd, BitTape.shifted, BitTape.atEnd, BitTape.ofList] using hv22
  · simpa [finish, hv24, hv31, hv33] using
      BitTape.append_write archive (!((row == previous) && s.registers 33))
  · have hab : Frame s b :=
      ((Frame.rewind s 15 (Or.inl rfl)).trans (Frame.pc _ 0)).trans
        ((Frame.rewind a 22 (Or.inr rfl)).trans (Frame.pc _ 0))
    have her : Frame e r := (Frame.clear {e with pc := 0}).trans (Frame.pc _ 0)
    have hru : Frame r u := (Frame.rewind r 15 (Or.inl rfl)).trans (Frame.pc _ 0)
    exact (((((hab.trans (Frame.compare hef)).trans her).trans hru).trans
      (Frame.copy hvf)).trans (Frame.pc _ 45)).trans (finish_frame v')

end Maxwell.Cost.SourceGrouping.Boundary
