import Maxwell.Cost.Division.Program

namespace Maxwell.Cost.Division

/-- Division changes only its five tapes and Boolean scratch registers. The
input divisor and dividend cells are preserved even while their heads scan. -/
def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (t.tapes 1).cells = (s.tapes 1).cells ∧ (t.tapes 3).cells = (s.tapes 3).cells ∧
  (∀ i, 5 ≤ i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, hd, hx, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kd, kx, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    kd.trans hd, kx.trans hx, fun i h5 => (kt i h5).trans (ht i h5),
    fun i h15 h24 h25 h26 h27 => (kg i h15 h24 h25 h26 h27).trans (hg i h15 h24 h25 h26 h27)⟩

/-- The statically checked write set of one instruction. -/
def InstructionSafe : BitRAMInstruction → Prop
  | .literal r _ | .bitXor r _ _ | .bitAnd r _ _ | .bitNot r _ =>
      r < 15 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27
  | .readTape _ r p =>
      (r < 15 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27) ∧
      (p < 15 ∨ p = 24 ∨ p = 25 ∨ p = 26 ∨ p = 27)
  | .writeTape t _ | .eraseTape t => t = 0 ∨ t = 2 ∨ t = 4
  | .tapeLeft t | .tapeRight t => t < 5
  | .branch _ _ _ | .jump _ | .halt => True
  | _ => False

instance (op : BitRAMInstruction) : Decidable (InstructionSafe op) := by
  cases op <;> unfold InstructionSafe <;> infer_instance

theorem program_safe : ∀ i : Fin program.code.length, InstructionSafe program.code[i] := by
  have h : program.code.all (fun op => decide (InstructionSafe op)) = true := by decide
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp h) _ (List.getElem_mem i.isLt))

private theorem register_frame (s : BitRAMState) (r : ℕ) (v : Bool)
    (hr : r < 15 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27) :
    Frame s (s.setRegister r v) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
  intro i hi h24 h25 h26 h27
  have hne : i ≠ r := by omega
  simp [BitRAMState.setRegister, hne]

private theorem read_frame (s : BitRAMState) (work r p : ℕ)
    (hr : r < 15 ∨ r = 24 ∨ r = 25 ∨ r = 26 ∨ r = 27)
    (hp : p < 15 ∨ p = 24 ∨ p = 25 ∨ p = 26 ∨ p = 27) :
    Frame s {s.setRegister r ((s.tapes work).read.getD false) with
      registers := Function.update (Function.update s.registers r
        ((s.tapes work).read.getD false)) p ((s.tapes work).read.isSome)} := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
  intro i hi h24 h25 h26 h27
  have hne : i ≠ r := by omega
  have hne' : i ≠ p := by omega
  simp [hne, hne']

private theorem tape_frame (s : BitRAMState) (j : ℕ) (u : BitTape) (hj : j < 5)
    (h1 : j = 1 → u.cells = (s.tapes 1).cells)
    (h3 : j = 3 → u.cells = (s.tapes 3).cells) : Frame s (s.setTape j u) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun _ _ _ _ _ _ => rfl⟩
  · by_cases h : 1 = j
    · subst j; simpa [BitRAMState.setTape] using h1 rfl
    · simp [BitRAMState.setTape, h]
  · by_cases h : 3 = j
    · subst j; simpa [BitRAMState.setTape] using h3 rfl
    · simp [BitRAMState.setTape, h]
  · intro i hi
    simp [BitRAMState.setTape, show i ≠ j by omega]

theorem instruction_frame (M : BitRAM) (input : List Bool) (tape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState} (op : BitRAMInstruction)
    (hsafe : InstructionSafe op) (hlookup : M.code[s.pc]? = some op)
    (h : M.next input tape s = some step) : Frame s step.state := by
  cases op <;> simp only [InstructionSafe] at hsafe
  all_goals simp only [BitRAM.next, hlookup, Option.some.injEq] at h
  all_goals try contradiction
  all_goals subst step
  case literal r v => exact register_frame s r v hsafe
  case bitXor r a b => exact register_frame s r _ hsafe
  case bitAnd r a b => exact register_frame s r _ hsafe
  case bitNot r a => exact register_frame s r _ hsafe
  case readTape w r p => exact read_frame s w r p hsafe.1 hsafe.2
  case writeTape w r =>
    exact tape_frame s w _ (by omega) (by intro h; omega) (by intro h; omega)
  case eraseTape w =>
    exact tape_frame s w _ (by omega) (by intro h; omega) (by intro h; omega)
  case tapeLeft w =>
    apply tape_frame s w _ hsafe
    · intro h; subst w; rfl
    · intro h; subst w; rfl
  case tapeRight w =>
    apply tape_frame s w _ hsafe
    · intro h; subst w; rfl
    · intro h; subst w; rfl
  case branch r y n => exact Frame.refl s
  case jump t => exact Frame.refl s

theorem next_frame (input : List Bool) (tape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState}
    (h : program.next input tape s = some step) : Frame s step.state := by
  have hpc := program.next_code_present input tape s step h
  exact instruction_frame program input tape program.code[s.pc]
    (program_safe ⟨s.pc, hpc⟩) (List.getElem?_eq_getElem hpc) h

theorem execution_frame (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ}
    (h : PricedSteps (program.next input tape) cost s t) : Frame s t := by
  induction h with
  | refl s => exact Frame.refl s
  | step h rest ih => exact (next_frame input tape h).trans ih

theorem sign_preserved (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ}
    (h : PricedSteps (program.next input tape) cost s t) : t.registers 23 = s.registers 23 := by
  exact (execution_frame input tape h).2.2.2.2.2.2.2.2 23 (by omega)
    (by omega) (by omega) (by omega) (by omega)

end Maxwell.Cost.Division
