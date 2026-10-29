import Maxwell.Cost.RealPrivate.Fresh
import Maxwell.Cost.RealPrivate.Allocator
import Maxwell.Cost.RealPrivate.Initialization

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

theorem Allocator.Frame.inputs {L : Layout} {origin : ℕ} {B : InputBuffer}
    {input : RAMInput} {s t : RAMState} (f : Allocator.Frame s t)
    (h : Inputs L origin B input s) : Inputs L origin B input t := by
  refine ⟨?_, ?_, ?_, ?_, h.real_low, h.index_low, h.real_high, h.index_high,
    ?_, ?_, h.real_outside, h.index_outside⟩
  · rw [f.indices realInputBase (by decide) (by decide) (by decide)]; exact h.real_base
  · rw [f.indices realInputLength (by decide) (by decide) (by decide)]; exact h.real_length
  · rw [f.indices indexInputBase (by decide) (by decide) (by decide)]; exact h.index_base
  · rw [f.indices indexInputLength (by decide) (by decide) (by decide)]; exact h.index_length
  · intro j hj; rw [f.words]; exact h.real_cells j hj
  · intro j hj
    rw [f.indices _ (by have := h.index_low; omega) (by have := h.index_low; omega)
      (by have := h.index_low; unfold originRegister; omega)]
    exact h.index_cells j hj

namespace FreshAllocation

theorem origin_high (width : ℕ) (hwidth : 8 ≤ width) : 256 ≤ 2^width :=
  Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hwidth

/-- Every private source cell is untouched by the actual prior caller
trace. The finite allocator changes only three lower index registers. -/
theorem empty_after_allocation {M : Machine} {input : RAMInput} {tape : ℕ → Bool}
    {width n : ℕ} {s t : RAMState}
    (trace : RealSimulation.VisitedSteps (M.next input tape)
      (RealSimulation.IndexWordWidth width) n RAMState.initial s)
    (code : CodeDestinationBound (2^width) M) (hwidth : 8 ≤ width)
    (frame : Allocator.Frame s t) : Cleanup.EmptyBank (2^width) t := by
  intro a
  have hh := origin_high width hwidth
  have ha := slot_ge_origin (2^width) 0 a
  have hf := fresh_of_initial_trace trace code le_rfl (slot (2^width) 0 a) ha
  constructor
  · rw [frame.words]; exact hf.1
  · rw [frame.indices _ (by omega) (by omega) (by unfold originRegister; omega)]
    exact hf.2

/-- Freshness is derived from the actual execution history and word width,
while the origin is computed by the actual finite doubling program. -/
theorem executes (M : Machine) (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {B : InputBuffer} {width n : ℕ} (s : Store)
    (trace : RealSimulation.VisitedSteps (M.next externalInput tape)
      (RealSimulation.IndexWordWidth width) n RAMState.initial s.val)
    (code : CodeDestinationBound (2^width) M) (hwidth : 8 ≤ width)
    (hw : s.val.indices 0 = width) (hi : Inputs L (2^width) B sourceInput s.val) :
    ∃ t, Executes externalInput tape Allocator.code (5*width+5) s t ∧
      t.val.indices originRegister = 2^width ∧ Cleanup.EmptyBank (2^width) t.val ∧
      Inputs L (2^width) B sourceInput t.val ∧ t.val.indices 0 = 0 ∧
      t.val.indices 3 = 1 ∧ Allocator.Frame s.val t.val := by
  obtain ⟨t, he, ho, h0, h3, hf⟩ := Allocator.executes externalInput tape width s hw
  exact ⟨t, he, ho, empty_after_allocation trace code hwidth hf, hf.inputs hi, h0, h3, hf⟩

/-- Allocation followed by the existing initialization code yields the
initial private source representation without a fresh-memory premise or
an incoming-random-cursor reset. Every executed instruction is charged. -/
theorem initializes (M : Machine) (externalInput sourceInput : RAMInput) (tape : ℕ → Bool)
    {L : Layout} {B : InputBuffer} {width n : ℕ} (s : Store)
    (trace : RealSimulation.VisitedSteps (M.next externalInput tape)
      (RealSimulation.IndexWordWidth width) n RAMState.initial s.val)
    (code : CodeDestinationBound (2^width) M) (hwidth : 8 ≤ width)
    (hw : s.val.indices 0 = width) (hi : Inputs L (2^width) B sourceInput s.val) :
    ∃ t, Executes externalInput tape (.seq Allocator.code initializeState) (5*width+21) s t ∧
      Represents (2^width) {RAMState.initial with randomCursor := s.val.randomCursor} [] t.val ∧
      Inputs L (2^width) B sourceInput t.val ∧
      t.val.indices statusRegister = 0 ∧ t.val.indices activeRegister = 1 ∧
      t.val.indices fuelRegister = s.val.indices fuelRegister ∧
      t.val.randomCursor = s.val.randomCursor ∧ t.val.output = s.val.output ∧
      t.val.indexOutput = s.val.indexOutput := by
  obtain ⟨a, he, ho, empty, hai, _, _, hf⟩ :=
    executes M externalInput sourceInput tape s trace code hwidth hw hi
  have hrep := initialized_represents (2^width) a (origin_high width hwidth) ho empty
  rw [hf.randomCursor] at hrep
  have hc := initialized_control a
  refine ⟨initialized a, ?_, hrep, initialized_inputs a hai, hc.2.1, hc.2.2.1,
    ?_, hc.2.2.2.1.trans hf.randomCursor, hc.2.2.2.2.1.trans hf.output,
    hc.2.2.2.2.2.trans hf.indexOutput⟩
  · convert he.seq (initializeState_executes externalInput tape a) using 1
  · exact hc.1.trans (hf.indices fuelRegister (by decide) (by decide) (by decide))

end FreshAllocation
end Maxwell.Cost.RealPrivate
