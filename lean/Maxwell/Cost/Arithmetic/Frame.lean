import Maxwell.Cost.Arithmetic
import Maxwell.Cost.Link

namespace Maxwell.Cost

/-- The complete state outside the adder's declared scratch locations. -/
def rippleFrame (s : BitRAMState) :=
  (s.address, s.inputHead, s.memory, s.randomCursor, s.output,
    (fun i : ℕ => s.registers (i + 12)), (fun i : ℕ => s.tapes (i + 3)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem rippleAdder_next_frame (input : List Bool) (tape : ℕ → Bool)
    (s t : BitRAMState) (extra : ℕ)
    (h : rippleAdder.next input tape s = some ⟨t, extra⟩) :
    rippleFrame t = rippleFrame s := by
  have hpc := rippleAdder.next_code_present input tape s ⟨t, extra⟩ h
  change s.pc < 18 at hpc
  interval_cases hp : s.pc <;>
    simp only [BitRAM.next, rippleAdder, hp, List.getElem?_cons_zero,
      List.getElem?_cons_succ] at h
  all_goals try contradiction
  all_goals
    simp only [Option.some.injEq, PricedStep.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [rippleFrame, setRegister_address, setRegister_inputHead,
      setRegister_memory, setRegister_randomCursor, setRegister_output,
      setRegister_registers, setRegister_tapes, setTape_address, setTape_inputHead,
      setTape_memory, setTape_randomCursor, setTape_output, setTape_registers,
      setTape_tapes]
  all_goals congr 1

theorem rippleAdder_execution_frame (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ}
    (h : PricedSteps (rippleAdder.next input tape) cost s t) :
    rippleFrame t = rippleFrame s :=
  h.conserved rippleFrame (rippleAdder_next_frame input tape)

/-- Input cells are read-only throughout the concrete routine. -/
def rippleInputCells (s : BitRAMState) := ((s.tapes 0).cells, (s.tapes 1).cells)

private def phaseZero (pc : ℕ) : ℤ := if pc = 14 ∨ pc = 15 then 1 else 0
private def phaseOne (pc : ℕ) : ℤ := if pc = 15 then 1 else 0

def rippleHeadFrame (s : BitRAMState) :=
  ((s.tapes 0).head - (s.tapes 2).head - phaseZero s.pc,
    (s.tapes 1).head - (s.tapes 2).head - phaseOne s.pc)

set_option maxRecDepth 4096 in
theorem rippleAdder_next_inputCells (input : List Bool) (tape : ℕ → Bool)
    (s t : BitRAMState) (extra : ℕ)
    (h : rippleAdder.next input tape s = some ⟨t, extra⟩) :
    rippleInputCells t = rippleInputCells s := by
  have hpc := rippleAdder.next_code_present input tape s ⟨t, extra⟩ h
  change s.pc < 18 at hpc
  interval_cases hp : s.pc <;>
    simp only [BitRAM.next, rippleAdder, hp, List.getElem?_cons_zero,
      List.getElem?_cons_succ] at h
  all_goals try contradiction
  all_goals
    simp only [Option.some.injEq, PricedStep.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [rippleInputCells]

set_option maxRecDepth 4096 in
theorem rippleAdder_next_headFrame (input : List Bool) (tape : ℕ → Bool)
    (s t : BitRAMState) (extra : ℕ)
    (h : rippleAdder.next input tape s = some ⟨t, extra⟩) :
    rippleHeadFrame t = rippleHeadFrame s := by
  have hpc := rippleAdder.next_code_present input tape s ⟨t, extra⟩ h
  change s.pc < 18 at hpc
  interval_cases hp : s.pc <;>
    simp only [BitRAM.next, rippleAdder, hp, List.getElem?_cons_zero,
      List.getElem?_cons_succ] at h
  all_goals try contradiction
  all_goals
    simp only [Option.some.injEq, PricedStep.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [rippleHeadFrame, phaseZero, phaseOne, BitTape.write, hp]
  all_goals try (split <;> simp_all)
  all_goals omega

set_option maxRecDepth 4096 in
theorem rippleAdder_next_pc (input : List Bool) (tape : ℕ → Bool)
    (s t : BitRAMState) (extra : ℕ)
    (h : rippleAdder.next input tape s = some ⟨t, extra⟩) : t.pc < 18 := by
  have hpc := rippleAdder.next_code_present input tape s ⟨t, extra⟩ h
  change s.pc < 18 at hpc
  interval_cases hp : s.pc <;>
    simp only [BitRAM.next, rippleAdder, hp, List.getElem?_cons_zero,
      List.getElem?_cons_succ] at h
  all_goals try contradiction
  all_goals
    simp only [Option.some.injEq, PricedStep.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [hp]
  all_goals split <;> omega

theorem rippleAdder_steps_pc (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ}
    (h : PricedSteps (rippleAdder.next input tape) cost s t) (hs : s.pc < 18) :
    t.pc < 18 := by
  induction h with
  | refl s => exact hs
  | step h rest ih => exact ih (rippleAdder_next_pc input tape _ _ _ h)

theorem rippleAdder_halt_pc (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc < 18) (h : rippleAdder.next input tape s = none) :
    s.pc = 17 := by
  interval_cases hp : s.pc <;> simp [rippleAdder, BitRAM.next, hp] at h ⊢

/-- Exact cell and head effects needed to call this routine repeatedly. -/
theorem rippleAdder_tape_effects (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ} {bits : List Bool}
    (h : PricedSteps (rippleAdder.next input tape) cost s t) (hs : s.pc = 0)
    (halt : rippleAdder.next input tape t = none)
    (hw : TapeWrites (s.tapes 2) (t.tapes 2) bits) :
    t.pc = 17 ∧ (t.tapes 0).cells = (s.tapes 0).cells ∧
      (t.tapes 1).cells = (s.tapes 1).cells ∧
      (t.tapes 0).head = (s.tapes 0).head + bits.length ∧
      (t.tapes 1).head = (s.tapes 1).head + bits.length := by
  have ht := rippleAdder_halt_pc input tape t (rippleAdder_steps_pc input tape h (by omega)) halt
  have hc := h.conserved rippleInputCells (rippleAdder_next_inputCells input tape)
  have hh := h.conserved rippleHeadFrame (rippleAdder_next_headFrame input tape)
  simp only [rippleInputCells, Prod.mk.injEq] at hc
  simp only [rippleHeadFrame, hs, ht, phaseZero, phaseOne] at hh
  norm_num at hh
  rcases hh with ⟨hzero, hone⟩
  have hout := hw.head
  exact ⟨ht, hc.1, hc.2, by omega, by omega⟩

end Maxwell.Cost
