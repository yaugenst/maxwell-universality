import Maxwell.Cost.RealSimulation.ControlPlacement

namespace Maxwell.Cost.RealSimulation.Control

/-- Every derivation of the finite structured semantics is simulated by
exactly the stated number of actual Real-RAM instructions. This theorem is
uniform in all surrounding code, input words and random draws. -/
theorem Executes.placed {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (execution : Executes input randomTape code cost s t)
    (machine : Machine) (base exitPC : ℕ) (placement : Placed machine code base exitPC) :
    Steps (machine.next input randomTape) cost (s.place base) (t.place exitPC) := by
  induction execution generalizing machine base exitPC with
  | skip s =>
    apply Steps.step (rest := Steps.refl (s.place exitPC))
    simp [Machine.next, Store.place, placement.skip]
  | call body s t cost steps halt =>
    have h := placement.call.call input randomTape steps halt
    simpa [RAMState.relocate, Store.place, Store.ofState, s.property] using h
  | seq firstRun secondRun ih1 ih2 =>
    exact (ih1 machine base _ placement.seq_first).trans
      (ih2 machine _ exitPC placement.seq_second)
  | @yes left right yes no cost s t test body ih =>
    have htest : Steps (machine.next input randomTape) 1
        (s.place base) (s.place (base + 1)) := by
      apply Steps.step (rest := Steps.refl _)
      simp [Machine.next, Store.place, placement.branch_head, test]
    exact htest.trans (ih machine (base + 1) exitPC placement.branch_yes)
  | @no left right yes no cost s t test body ih =>
    have htest : Steps (machine.next input randomTape) 1
        (s.place base) (s.place (base + 1 + yes.size)) := by
      apply Steps.step (rest := Steps.refl _)
      simp [Machine.next, Store.place, placement.branch_head, test]
    exact htest.trans (ih machine _ exitPC placement.branch_no)
  | done test =>
    apply Steps.step (rest := Steps.refl _)
    simp [Machine.next, Store.place, placement.loop_head, test]
  | @more left right body a b s t u test bodyRun rest ih1 ih2 =>
    have htest : Steps (machine.next input randomTape) 1
        (s.place base) (s.place (base + 1)) := by
      apply Steps.step (rest := Steps.refl _)
      simp [Machine.next, Store.place, placement.loop_head, test]
    exact (htest.trans (ih1 machine (base + 1) base placement.loop_body)).trans
      (ih2 machine base exitPC placement)

/-- Compile a complete statement with a literal final halt. -/
theorem Executes.compiled_steps {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (execution : Executes input randomTape code cost s t) :
    Steps (code.compile.next input randomTape) cost s.val (t.place code.size) := by
  simpa using execution.placed code.compile 0 code.size code.compile_placed

/-- The compiled program really terminates under any cap exceeding the
proved cost, and reports exactly that cost. No runtime-label assumption is
used to turn the structured semantics into a machine execution. -/
theorem Executes.compiled_run {input : RAMInput} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store}
    (execution : Executes input randomTape code cost s t) (fuel : ℕ) (hfuel : cost < fuel) :
    (runCapped (code.compile.next input randomTape) fuel s.val).finished = some (t.place code.size) ∧
    (runCapped (code.compile.next input randomTape) fuel s.val).instructions = cost := by
  apply runCapped_of_terminates_ge _ (execution.compiled_steps.terminates
    (Terminates.halt _ (by simp [Machine.next, Store.place, code.compile_halt])))
  omega

end Maxwell.Cost.RealSimulation.Control
