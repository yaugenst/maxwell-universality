import Maxwell.Cost.RealPrivate.Verified
import Maxwell.Cost.RealPrivate.FreshAllocation

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

def allocatedCode (L : Layout) (M : Machine) : Code := .seq Allocator.code (reusableCode L M)
def allocatedProgram (L : Layout) (M : Machine) : Machine := (allocatedCode L M).compile
def allocatedBudget (L : Layout) (M : Machine) (width fuel : ℕ) : ℕ :=
  5 * width + 5 + reusableBudget L M fuel

/-- The first invocation derives freshness from the actual bounded caller
history. The allocator, source simulation, cap and cleanup are all parts
of one fixed finite program; no fresh workspace is supplied as an oracle. -/
theorem allocated_executes (caller M : Machine) (L : Layout)
    (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {B : InputBuffer} {width n : ℕ} (fuel : ℕ) (s : Store)
    (trace : RealSimulation.VisitedSteps (caller.next externalInput tape)
      (RealSimulation.IndexWordWidth width) n RAMState.initial s.val)
    (destinations : CodeDestinationBound (2 ^ width) caller) (high : 8 ≤ width)
    (hw : s.val.indices 0 = width) (hi : Inputs L (2 ^ width) B sourceInput s.val)
    (hf : s.val.indices fuelRegister = fuel) :
    ∃ cost allocated t stop, cost ≤ allocatedBudget L M width fuel ∧
      Executes externalInput tape (allocatedCode L M) cost s t ∧
      Allocator.Frame s.val allocated.val ∧
      ReusablePost L M sourceInput tape (2 ^ width) fuel B allocated t stop ∧
      (runCapped (M.next sourceInput tape) fuel (sourceStart s)).finished =
        if t.val.indices statusRegister = 1 then some stop else none := by
  obtain ⟨a, ea, ho, empty, hai, _, _, frame⟩ :=
    FreshAllocation.executes caller externalInput sourceInput tape s trace destinations high hw hi
  have haFuel : a.val.indices fuelRegister = fuel :=
    (frame.indices fuelRegister (by decide) (by decide) (by decide)).trans hf
  obtain ⟨cost, t, stop, hc, he, post⟩ := reusable_executes L M externalInput sourceInput tape fuel a
    (FreshAllocation.origin_high width high) ho empty hai haFuel
  refine ⟨5 * width + 5 + cost, a, t, stop, ?_, ea.seq he, frame, post, ?_⟩
  · unfold allocatedBudget; omega
  · simpa only [sourceStart, frame.randomCursor] using post.finished

theorem allocated_run (caller M : Machine) (L : Layout)
    (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {B : InputBuffer} {width n : ℕ} (fuel : ℕ) (s : Store)
    (trace : RealSimulation.VisitedSteps (caller.next externalInput tape)
      (RealSimulation.IndexWordWidth width) n RAMState.initial s.val)
    (destinations : CodeDestinationBound (2 ^ width) caller) (high : 8 ≤ width)
    (hw : s.val.indices 0 = width) (hi : Inputs L (2 ^ width) B sourceInput s.val)
    (hf : s.val.indices fuelRegister = fuel) :
    ∃ allocated t stop,
      (runCapped ((allocatedProgram L M).next externalInput tape)
        (allocatedBudget L M width fuel + 1) s.val).finished = some (t.place (allocatedCode L M).size) ∧
      (runCapped ((allocatedProgram L M).next externalInput tape)
        (allocatedBudget L M width fuel + 1) s.val).instructions ≤ allocatedBudget L M width fuel ∧
      Allocator.Frame s.val allocated.val ∧
      ReusablePost L M sourceInput tape (2 ^ width) fuel B allocated t stop ∧
      (runCapped (M.next sourceInput tape) fuel (sourceStart s)).finished =
        if t.val.indices statusRegister = 1 then some stop else none := by
  obtain ⟨cost, a, t, stop, hc, he, frame, post, finished⟩ :=
    allocated_executes caller M L externalInput sourceInput tape fuel s trace destinations high hw hi hf
  obtain ⟨hr, hcost⟩ := he.compiled_run (allocatedBudget L M width fuel + 1) (by omega)
  refine ⟨a, t, stop, hr, ?_, frame, post, finished⟩
  unfold allocatedProgram
  rw [hcost]
  exact hc

end Maxwell.Cost.RealPrivate
