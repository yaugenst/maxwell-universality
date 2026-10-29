import Maxwell.Cost.RealSimulation.Simulation
import Maxwell.Cost.RealSimulation.Initialization
import Maxwell.Cost.RunPriced.Converse

namespace Maxwell.Cost.RealSimulation

open Control

def machine (M : BitRAM) : Machine := compiled (footprint M.code) Address.code M
def initializationCost (M : BitRAM) : ℕ :=
  2 * ((footprint M.code).registerCount + (footprint M.code).tapeCount + 7)
def budget (M : BitRAM) (sourceFuel : ℕ) : ℕ :=
  initializationCost M + (dispatchConstant M + 1) * sourceFuel + terminalConstant M + 1

/-- Uniform finite-machine simulation with its initialization charged.
The entry condition describes only the caller's encoded input/fresh banks;
it does not assume a source solution, execution trace, or runtime oracle. -/
theorem machine_terminates (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {b : BitRAMState} {n : ℕ}
    (source : PricedSteps (M.next bits tape) n BitRAMState.initial b)
    (halt : M.next bits tape b = none) (cap : n ≤ center)
    (s : Store) (entry : Initialization.Entry (footprint M.code) origin center bits s) :
    ∃ cost t, cost ≤ initializationCost M + (dispatchConstant M + 1) * n + terminalConstant M ∧
      Terminates ((machine M).next input tape) cost s.val t ∧
      Represents (footprint M.code) origin center bits b t := by
  obtain ⟨u, ei, hu⟩ := initializeState_executes input tape s entry
  obtain ⟨cost, t, hc, he, hr⟩ := interpreter_priced M input tape source halt 0
    SourceBounds.initial (by simpa using cap) u hu
  have hall := ei.seq he
  let code : Code := .seq (initializeState (footprint M.code))
    (interpreter (footprint M.code) Address.code M)
  refine ⟨initializationCost M + cost, t.place code.size, by unfold initializationCost; omega,
    hall.compiled_steps.terminates (Terminates.halt _ ?_), hr.congr (fun _ _ => rfl) rfl⟩
  change code.compile.next input tape (t.place code.size) = none
  simp [Machine.next, Store.place, Code.compile_halt]

/-- A successful capped BitRAM run transfers to a successful capped RealRAM
run of this one fixed finite program. The target cap is affine in source fuel. -/
theorem machine_run (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {b : BitRAMState} (sourceFuel : ℕ)
    (source : (M.run bits tape sourceFuel).finished = some b) (cap : sourceFuel ≤ center)
    (s : Store) (entry : Initialization.Entry (footprint M.code) origin center bits s) :
    ∃ t, (runCapped ((machine M).next input tape) (budget M sourceFuel) s.val).finished = some t ∧
      (runCapped ((machine M).next input tape) (budget M sourceFuel) s.val).instructions <
        budget M sourceFuel ∧ Represents (footprint M.code) origin center bits b t := by
  obtain ⟨hp, hh⟩ := runPriced_pricedSteps (M.next bits tape) sourceFuel
    BitRAMState.initial b source
  have hb := M.run_all_inputs_le bits tape sourceFuel
  simp only [BitRAM.run] at hb
  obtain ⟨cost, t, hc, ht, hr⟩ := machine_terminates M input tape hp hh (hb.trans cap) s entry
  have hn : cost + 1 ≤ budget M sourceFuel := by
    unfold budget
    have hmul := Nat.mul_le_mul_left (dispatchConstant M + 1) hb
    omega
  have result := runCapped_of_terminates_ge _ ht (budget M sourceFuel) hn
  exact ⟨t, result.1, by rw [result.2]; omega, hr⟩

/-- Every simulated output is the actual source output in chronological
order in the caller's output bank, including the exact output length. -/
theorem machine_run_output (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {b : BitRAMState} (sourceFuel : ℕ)
    (source : (M.run bits tape sourceFuel).finished = some b) (cap : sourceFuel ≤ center)
    (s : Store) (entry : Initialization.Entry (footprint M.code) origin center bits s) :
    ∃ t, (runCapped ((machine M).next input tape) (budget M sourceFuel) s.val).finished = some t ∧
      t.indices outputLength = b.output.length ∧
      (∀ j < b.output.length,
        t.indices ((footprint M.code).slot origin (footprint M.code).outputBank j) =
          (b.output.reverse[j]?.getD false).toNat) ∧
      t.randomCursor = b.randomCursor := by
  obtain ⟨t, ht, _, hr⟩ := machine_run M input tape sourceFuel source cap s entry
  exact ⟨t, ht, hr.output_length, hr.output_cells, hr.random_cursor⟩

end Maxwell.Cost.RealSimulation
