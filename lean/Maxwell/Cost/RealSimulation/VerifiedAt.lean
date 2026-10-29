import Maxwell.Cost.RealSimulation.Verified
import Maxwell.Cost.RealSimulation.RandomOffset

namespace Maxwell.Cost.RealSimulation

open Control

/-- The same finite code can follow a previous randomized call. The source
sees the unused suffix of the actual tape; the real machine never resets its
random cursor and initialization still costs the same fixed number of steps. -/
theorem machine_terminates_at (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center randomBase : ℕ} {bits : List Bool} {b : BitRAMState} {n : ℕ}
    (source : PricedSteps (M.next bits (RandomOffset.shiftTape randomBase tape)) n
      BitRAMState.initial b)
    (halt : M.next bits (RandomOffset.shiftTape randomBase tape) b = none)
    (cap : randomBase + n ≤ center)
    (s : Store) (entry : Initialization.EntryAt (footprint M.code) origin center bits randomBase s) :
    ∃ cost t, cost ≤ initializationCost M + (dispatchConstant M + 1) * n + terminalConstant M ∧
      Terminates ((machine M).next input tape) cost s.val t ∧
      Represents (footprint M.code) origin center bits (RandomOffset.shiftCursor randomBase b) t := by
  obtain ⟨u, ei, hu⟩ := initializeState_executes_at input tape s entry
  have hp := RandomOffset.priced_shift source
  have hh := (RandomOffset.halt_shift_iff M bits tape randomBase b).mpr halt
  have hi : RandomOffset.shiftCursor randomBase BitRAMState.initial =
      {BitRAMState.initial with randomCursor := randomBase} := by
    simp [RandomOffset.shiftCursor, BitRAMState.initial]
  rw [hi] at hp
  obtain ⟨cost, t, hc, he, hr⟩ := interpreter_priced M input tape hp hh randomBase
    (SourceBounds.initial_at randomBase) cap u hu
  have hall := ei.seq he
  let code : Code := .seq (initializeState (footprint M.code))
    (interpreter (footprint M.code) Address.code M)
  refine ⟨initializationCost M + cost, t.place code.size, by unfold initializationCost; omega,
    hall.compiled_steps.terminates (Terminates.halt _ ?_), hr.congr (fun _ _ => rfl) rfl⟩
  change code.compile.next input tape (t.place code.size) = none
  simp [Machine.next, Store.place, Code.compile_halt]

theorem machine_run_at (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center randomBase : ℕ} {bits : List Bool} {b : BitRAMState} (sourceFuel : ℕ)
    (source : (M.run bits (RandomOffset.shiftTape randomBase tape) sourceFuel).finished = some b)
    (cap : randomBase + sourceFuel ≤ center)
    (s : Store) (entry : Initialization.EntryAt (footprint M.code) origin center bits randomBase s) :
    ∃ t, (runCapped ((machine M).next input tape) (budget M sourceFuel) s.val).finished = some t ∧
      (runCapped ((machine M).next input tape) (budget M sourceFuel) s.val).instructions <
        budget M sourceFuel ∧
      Represents (footprint M.code) origin center bits (RandomOffset.shiftCursor randomBase b) t := by
  obtain ⟨hp, hh⟩ := runPriced_pricedSteps
    (M.next bits (RandomOffset.shiftTape randomBase tape)) sourceFuel BitRAMState.initial b source
  have hb := M.run_all_inputs_le bits (RandomOffset.shiftTape randomBase tape) sourceFuel
  simp only [BitRAM.run] at hb
  obtain ⟨cost, t, hc, ht, hr⟩ := machine_terminates_at M input tape hp hh (by omega) s entry
  have hn : cost + 1 ≤ budget M sourceFuel := by
    unfold budget
    have hmul := Nat.mul_le_mul_left (dispatchConstant M + 1) hb
    omega
  have result := runCapped_of_terminates_ge _ ht (budget M sourceFuel) hn
  exact ⟨t, result.1, by rw [result.2]; omega, hr⟩

end Maxwell.Cost.RealSimulation
