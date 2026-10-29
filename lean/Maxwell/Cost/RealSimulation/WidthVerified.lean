import Maxwell.Cost.RealSimulation.WidthInitialization
import Maxwell.Cost.RunPriced.Converse

namespace Maxwell.Cost.RealSimulation
open Control

/-- A fixed finite Real-RAM program simulates the actual priced source run.
All target index words, including intermediate addresses, have linear width
in the explicit source width parameter. Constants depend only on the fixed
source program. -/
theorem width_machine_terminates (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center randomBase W : ℕ} {bits : List Bool} {b : BitRAMState} {n : ℕ}
    (source : PricedSteps (M.next bits tape) n
      {BitRAMState.initial with randomCursor := randomBase} b)
    (halt : M.next bits tape b = none)
    (width : PrefixAddressBound M bits tape
      {BitRAMState.initial with randomCursor := randomBase} n W)
    (cap : randomBase + n ≤ center) (center_bound : 2 * center ≤ 2 ^ W)
    (pc_bound : programPCCap M ≤ 2 ^ W) (two : 2 ≤ 2 ^ W)
    (literals : IndexWidth.LiteralBound (2 ^ W) (widthMachine M))
    (inputs : IndexWidth.InputBound (2 ^ W) input)
    (s : Store) (entry : Initialization.EntryAt (footprint M.code) origin center bits randomBase s)
    (bound : IndexWidth.IndexBound (2 ^ W) s.val) :
    ∃ cost t, cost ≤ widthInitializationCost M + widthConstant M * n + terminalConstant M + 27 ∧
      Terminates ((widthMachine M).next input tape) cost s.val t ∧
      Represents (footprint M.code) origin center bits b t ∧
      VisitedSteps ((widthMachine M).next input tape)
        (IndexWordWidth ((completeWidthConstant M + 1) * (W + 1))) cost s.val t := by
  obtain ⟨u, ei, hu, hb⟩ := width_initialization M input tape s entry bound
    (by omega) center_bound two
  have placed : Placed (widthMachine M) (widthProgram M) 0 (widthProgram M).size :=
    (widthProgram M).compile_placed
  obtain ⟨cost, t, hc, he, hr, hv⟩ := width_interpreter_priced M input tape source halt width
    randomBase (SourceBounds.initial_at randomBase) cap center_bound pc_bound two
    (widthMachine M) (widthPrefix M).size (widthProgram M).size (by simpa using placed.seq_second)
    literals inputs u hu hb
  have ci : widthInitializationCost M ≤ completeWidthConstant M * (W + 1) := by
    unfold completeWidthConstant
    nlinarith
  have vi := visited_segment_width (s := s.place 0) bound literals inputs ci
    (ei.placed (widthMachine M) 0 (widthPrefix M).size (by simpa using placed.seq_first))
  have hv' := hv.mono (Q := IndexWordWidth ((completeWidthConstant M + 1) * (W + 1))) (by
    intro v hv j
    have hh := hv j
    unfold completeWidthConstant
    nlinarith)
  have allVisited : VisitedSteps ((widthMachine M).next input tape)
      (IndexWordWidth ((completeWidthConstant M + 1) * (W + 1)))
      (widthInitializationCost M + cost) s.val (t.place (widthProgram M).size) := by
    simpa only [Store.place_zero] using vi.trans hv'
  refine ⟨widthInitializationCost M + cost, t.place (widthProgram M).size, by omega,
    ?_, hr.congr (fun _ _ => rfl) rfl, ?_⟩
  · exact allVisited.steps.terminates (Terminates.halt _ (by
      simp [widthMachine, Machine.next, Store.place, Code.compile_halt]))
  · exact allVisited

def widthBudget (M : BitRAM) (sourceFuel : ℕ) : ℕ :=
  widthInitializationCost M + widthConstant M * sourceFuel + terminalConstant M + 28

theorem width_machine_run (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center randomBase W : ℕ} {bits : List Bool} {b : BitRAMState} (sourceFuel : ℕ)
    (source : (runPriced (M.next bits tape) sourceFuel
      {BitRAMState.initial with randomCursor := randomBase}).finished = some b)
    (width : PrefixAddressBound M bits tape
      {BitRAMState.initial with randomCursor := randomBase} sourceFuel W)
    (cap : randomBase + sourceFuel ≤ center) (center_bound : 2 * center ≤ 2 ^ W)
    (pc_bound : programPCCap M ≤ 2 ^ W) (two : 2 ≤ 2 ^ W)
    (literals : IndexWidth.LiteralBound (2 ^ W) (widthMachine M))
    (inputs : IndexWidth.InputBound (2 ^ W) input)
    (s : Store) (entry : Initialization.EntryAt (footprint M.code) origin center bits randomBase s)
    (bound : IndexWidth.IndexBound (2 ^ W) s.val) :
    ∃ cost t, cost < widthBudget M sourceFuel ∧
      (runCapped ((widthMachine M).next input tape) (widthBudget M sourceFuel) s.val).finished = some t ∧
      (runCapped ((widthMachine M).next input tape) (widthBudget M sourceFuel) s.val).instructions = cost ∧
      Represents (footprint M.code) origin center bits b t ∧
      VisitedSteps ((widthMachine M).next input tape)
        (IndexWordWidth ((completeWidthConstant M + 1) * (W + 1))) cost s.val t := by
  obtain ⟨hp, hh⟩ := runPriced_pricedSteps (M.next bits tape) sourceFuel _ b source
  have hn := runPriced_le (M.next bits tape) sourceFuel
    {BitRAMState.initial with randomCursor := randomBase}
  obtain ⟨cost, t, hc, ht, hr, hv⟩ := width_machine_terminates M input tape hp hh
    (fun k u hk hu => width k u (hk.trans hn) hu) (by omega) center_bound pc_bound two
    literals inputs s entry bound
  have cb : cost < widthBudget M sourceFuel := by
    have := Nat.mul_le_mul_left (widthConstant M) hn
    unfold widthBudget
    omega
  have run := runCapped_of_terminates_ge _ ht (widthBudget M sourceFuel) (by omega)
  exact ⟨cost, t, cb, run.1, run.2, hr, hv⟩

end Maxwell.Cost.RealSimulation
