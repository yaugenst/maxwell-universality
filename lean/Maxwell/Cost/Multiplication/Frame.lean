import Maxwell.Cost.Multiplication.Correctness

namespace Maxwell.Cost.HornerMultiply

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 4 ≤ i → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.refl (s : BitRAMState) : Frame s s := by simp [Frame]

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h4 => (kt i h4).trans (ht i h4),
    fun i h15 h24 h25 h26 h27 => (kg i h15 h24 h25 h26 h27).trans (hg i h15 h24 h25 h26 h27)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem next_frame (input : List Bool) (tape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState}
    (h : program.next input tape s = some step) : Frame s step.state := by
  have hpc := program.next_code_present input tape s step h
  rw [program_length] at hpc
  interval_cases hp : s.pc <;>
    simp [BitRAM.next, program, hp, RewindOvershoot.program, Rewind.program,
      RewindOvershoot.preamble, BitRAM.link, rippleAdder, TapeOps.clear,
      TapeOps.copyClear, BitRAMInstruction.relocate] at h
  all_goals subst step
  all_goals simp [Frame, BitRAMState.setRegister, BitRAMState.setTape, Function.update_apply]
  all_goals intros
  all_goals try omega
  all_goals split_ifs <;> simp_all

theorem execution_frame (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ}
    (h : PricedSteps (program.next input tape) cost s t) : Frame s t := by
  induction h with
  | refl s => exact Frame.refl s
  | step h rest ih => exact (next_frame input tape h).trans ih

theorem sign_preserved (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ}
    (h : PricedSteps (program.next input tape) cost s t) : t.registers 23 = s.registers 23 := by
  exact (execution_frame input tape h).2.2.2.2.2.2 23 (by omega)
    (by omega) (by omega) (by omega) (by omega)

end Maxwell.Cost.HornerMultiply
