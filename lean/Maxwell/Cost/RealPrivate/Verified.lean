import Maxwell.Cost.RealPrivate.Cap
import Maxwell.Cost.RealPrivate.Initialization
import Maxwell.Cost.RealPrivate.SourceBounds

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

def reusableCode (L : Layout) (M : Machine) : Code :=
  .seq initializeState (.seq (cappedInterpreter L M) cleanup)

def reusableProgram (L : Layout) (M : Machine) : Machine := (reusableCode L M).compile

def reusableBudget (L : Layout) (M : Machine) (fuel : ℕ) : ℕ :=
  16 + loopBound L M * (fuel + 1) + 37 * fuel + 5

noncomputable def sourceStart (s : Store) : RAMState :=
  {RAMState.initial with randomCursor := s.val.randomCursor}

structure OutputBuffer (origin : ℕ) (source : RAMState) (target : RAMState) : Prop where
  real_length : target.indices realOutputLength = source.output.length
  index_length : target.indices indexOutputLength = source.indexOutput.length
  real_cells : ∀ j < source.output.length,
    target.words (slot origin 1 j) = source.output.reverse[j]?.getD 0
  index_cells : ∀ j < source.indexOutput.length,
    target.indices (slot origin 1 j) = source.indexOutput.reverse[j]?.getD 0
  random_cursor : target.randomCursor = source.randomCursor

theorem Represents.outputBuffer {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : RAMState} (h : Represents origin source written s) : OutputBuffer origin source s :=
  ⟨h.real_output_length, h.index_output_length, h.real_output, h.index_output, h.random_cursor⟩

theorem Cleanup.Frame.outputBuffer {origin : ℕ} {source : RAMState} {s t : RAMState}
    (h : Cleanup.Frame origin s t) (high : 256 ≤ origin) (hs : OutputBuffer origin source s) :
    OutputBuffer origin source t := by
  have hn (j : ℕ) (hj : j < 256) (a : ℕ) : j ≠ slot origin 0 a :=
    (slot_ne_small high 0 a j hj).symm
  refine ⟨?_, ?_, ?_, ?_, h.randomCursor.trans hs.random_cursor⟩
  · rw [h.indices realOutputLength (by decide) (by decide) (by decide) (by decide)
      (hn realOutputLength (by decide))]
    exact hs.real_length
  · rw [h.indices indexOutputLength (by decide) (by decide) (by decide) (by decide)
      (hn indexOutputLength (by decide))]
    exact hs.index_length
  · intro j hj; rw [h.word_bank high 1 (by decide) (by decide)]; exact hs.real_cells j hj
  · intro j hj; rw [h.index_bank high 1 (by decide) (by decide)]; exact hs.index_cells j hj

theorem initialized_runFrame (s : Store) (origin : ℕ) :
    RunFrame origin s.val (initialized s).val := by
  refine ⟨fun _ _ _ => rfl, ?_, rfl, rfl⟩
  intro j hj _ hm
  have hn6 : j ≠ 6 := by omega
  have hn7 : j ≠ 7 := by omega
  have hn166 : j ≠ 166 := by omega
  have hn167 : j ≠ 167 := by omega
  have hn168 : j ≠ 168 := by omega
  have hn169 : j ≠ 169 := by omega
  have hn170 : j ≠ 170 := by omega
  have hn171 : j ≠ 171 := by omega
  simp [initialized, zeroRegister, oneRegister, statusRegister, realOutputLength,
    indexOutputLength, logLength, sourcePC, activeRegister,
    hn6, hn7, hn166, hn167, hn168, hn169, hn170, hn171]

structure ReusablePost (L : Layout) (M : Machine) (sourceInput : RAMInput) (tape : ℕ → Bool)
    (origin fuel : ℕ) (B : InputBuffer) (s t : Store) (stop : RAMState) : Prop where
  output : OutputBuffer origin stop t.val
  empty : Cleanup.EmptyBank origin t.val
  inputs : Inputs L origin B sourceInput t.val
  origin_word : t.val.indices originRegister = origin
  real_bound : stop.output.length ≤ fuel
  index_bound : stop.indexOutput.length ≤ fuel
  random_lower : s.val.randomCursor ≤ t.val.randomCursor
  random_upper : t.val.randomCursor ≤ s.val.randomCursor + fuel
  log_bound : t.val.indices logLength ≤ fuel
  active : t.val.indices activeRegister = 0
  status : t.val.indices statusRegister = 0 ∨ t.val.indices statusRegister = 1
  finished : (runCapped (M.next sourceInput tape) fuel (sourceStart s)).finished =
    if t.val.indices statusRegister = 1 then some stop else none
  trace : Steps (M.next sourceInput tape)
    (runCapped (M.next sourceInput tape) fuel (sourceStart s)).instructions (sourceStart s) stop
  frame : RunFrame origin s.val t.val

/-- One fixed program initializes the virtual solver, enforces the cap by
ordinary instructions, and clears every private source cell using its
charged write log. Its output banks remain available after cleanup. -/
theorem reusable_executes (L : Layout) (M : Machine)
    (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {B : InputBuffer} (fuel : ℕ) (s : Store)
    (high : 256 ≤ origin) (ho : s.val.indices originRegister = origin)
    (empty : Cleanup.EmptyBank origin s.val) (hi : Inputs L origin B sourceInput s.val)
    (hf : s.val.indices fuelRegister = fuel) :
    ∃ cost t stop, cost ≤ reusableBudget L M fuel ∧
      Executes externalInput tape (reusableCode L M) cost s t ∧
      ReusablePost L M sourceInput tape origin fuel B s t stop := by
  have hrep := initialized_represents origin s high ho empty
  have hinput := initialized_inputs s hi
  have hcontrol := initialized_control s
  obtain ⟨cost, u, stop, finalLog, hc, he, post⟩ :=
    cappedInterpreter_executes L M externalInput sourceInput tape fuel (sourceStart s) [] (initialized s)
      hrep hinput (initial_covered _) (hcontrol.1.trans hf) hcontrol.2.1 hcontrol.2.2.1
  obtain ⟨t, clean, cleanEmpty, config, _, cleanFrame⟩ :=
    Cleanup.executes externalInput tape origin stop finalLog u post.represents post.covered
  have outputs := cleanFrame.outputBuffer high post.represents.outputBuffer
  have logbound : finalLog.length ≤ fuel := by simpa using post.log_bound
  have bounds := SourceBounds.initial_prefix_bounds post.trace
    (runCapped_le (M.next sourceInput tape) fuel (sourceStart s))
  have frame := (initialized_runFrame s origin).trans
    (post.frame.trans cleanFrame.caller.runFrame)
  have sameStatus : t.val.indices statusRegister = u.val.indices statusRegister :=
    cleanFrame.caller.indices statusRegister (by decide) (by unfold statusRegister; omega) (by left; decide)
  have sameActive : t.val.indices activeRegister = u.val.indices activeRegister :=
    cleanFrame.caller.indices activeRegister (by decide) (by unfold activeRegister; omega) (by right; decide)
  refine ⟨16 + (cost + (37 * finalLog.length + 5)), t, stop, ?_,
    (initializeState_executes externalInput tape s).seq (he.seq clean), outputs, cleanEmpty,
    frame.inputs high hi, config.origin_word, bounds.1, bounds.2.1, ?_, ?_, ?_,
    sameActive.trans post.active, ?_, ?_, post.trace, frame⟩
  · unfold reusableBudget; omega
  · rw [outputs.random_cursor]; exact bounds.2.2.1
  · rw [outputs.random_cursor]; exact bounds.2.2.2
  · rw [config.length]; exact logbound
  · rw [sameStatus]; exact post.status
  · rw [sameStatus]; exact post.finished

theorem reusable_run (L : Layout) (M : Machine)
    (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {origin : ℕ} {B : InputBuffer} (fuel : ℕ) (s : Store)
    (high : 256 ≤ origin) (ho : s.val.indices originRegister = origin)
    (empty : Cleanup.EmptyBank origin s.val) (hi : Inputs L origin B sourceInput s.val)
    (hf : s.val.indices fuelRegister = fuel) :
    ∃ t stop, (runCapped ((reusableProgram L M).next externalInput tape)
        (reusableBudget L M fuel + 1) s.val).finished = some (t.place (reusableCode L M).size) ∧
      (runCapped ((reusableProgram L M).next externalInput tape)
        (reusableBudget L M fuel + 1) s.val).instructions ≤ reusableBudget L M fuel ∧
      ReusablePost L M sourceInput tape origin fuel B s t stop := by
  obtain ⟨cost, t, stop, hc, he, post⟩ := reusable_executes L M externalInput sourceInput tape
    fuel s high ho empty hi hf
  obtain ⟨hr, hcost⟩ := he.compiled_run (reusableBudget L M fuel + 1) (by omega)
  exact ⟨t, stop, hr, by unfold reusableProgram; rw [hcost]; exact hc, post⟩

end Maxwell.Cost.RealPrivate
