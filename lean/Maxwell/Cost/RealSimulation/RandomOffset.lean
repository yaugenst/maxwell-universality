import Maxwell.Cost.RealSimulation.SourceBounds

namespace Maxwell.Cost.RealSimulation

namespace RandomOffset

/-- Continue from a caller's consumed random-tape prefix. All source data and
control fields retain their original values. -/
def shiftCursor (base : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with randomCursor := base + s.randomCursor}

def shiftTape (base : ℕ) (tape : ℕ → Bool) (j : ℕ) : Bool := tape (base + j)

def shiftPriced (base : ℕ) (p : PricedStep BitRAMState) : PricedStep BitRAMState :=
  {p with state := shiftCursor base p.state}

@[simp] theorem shiftCursor_output (base : ℕ) (s : BitRAMState) :
    (shiftCursor base s).output = s.output := rfl

@[simp] theorem shiftCursor_randomCursor (base : ℕ) (s : BitRAMState) :
    (shiftCursor base s).randomCursor = base + s.randomCursor := rfl

/-- The concrete instruction interpreter commutes with a random-tape offset;
the charged address and instruction costs are unchanged. -/
theorem next_shift (M : BitRAM) (bits : List Bool) (tape : ℕ → Bool)
    (base : ℕ) (s : BitRAMState) :
    M.next bits tape (shiftCursor base s) =
      (M.next bits (shiftTape base tape) s).map (shiftPriced base) := by
  cases hc : M.code[s.pc]? with
  | none => simp [BitRAM.next, shiftCursor, hc]
  | some op =>
    cases op <;> simp [BitRAM.next, shiftCursor, shiftPriced, shiftTape, hc,
      BitRAMState.setRegister, BitRAMState.setTape, Nat.add_assoc]
    rfl

theorem priced_shift {M : BitRAM} {bits : List Bool} {tape : ℕ → Bool}
    {base n : ℕ} {s t : BitRAMState}
    (h : PricedSteps (M.next bits (shiftTape base tape)) n s t) :
    PricedSteps (M.next bits tape) n (shiftCursor base s) (shiftCursor base t) := by
  induction h with
  | refl s => exact PricedSteps.refl _
  | @step n extra s t u h rest ih =>
    apply PricedSteps.step (t := shiftCursor base t) (extra := extra) _ ih
    rw [next_shift, h]
    rfl

theorem halt_shift_iff (M : BitRAM) (bits : List Bool) (tape : ℕ → Bool)
    (base : ℕ) (s : BitRAMState) :
    M.next bits tape (shiftCursor base s) = none ↔
      M.next bits (shiftTape base tape) s = none := by
  rw [next_shift]
  simp

theorem terminates_shift {M : BitRAM} {bits : List Bool} {tape : ℕ → Bool}
    {base n : ℕ} {s t : BitRAMState}
    (h : PricedSteps (M.next bits (shiftTape base tape)) n s t)
    (halt : M.next bits (shiftTape base tape) t = none) :
    Terminates (microNext (M.next bits tape)) n
      (.ready (shiftCursor base s)) (.ready (shiftCursor base t)) :=
  (priced_shift h).terminates ((halt_shift_iff M bits tape base t).mpr halt)

theorem runPriced_shift {M : BitRAM} {bits : List Bool} {tape : ℕ → Bool}
    {base n : ℕ} {s t : BitRAMState}
    (h : PricedSteps (M.next bits (shiftTape base tape)) n s t)
    (halt : M.next bits (shiftTape base tape) t = none) (fuel : ℕ) (hf : n + 1 ≤ fuel) :
    (runPriced (M.next bits tape) fuel (shiftCursor base s)).finished =
        some (shiftCursor base t) ∧
      (runPriced (M.next bits tape) fuel (shiftCursor base s)).instructions = n :=
  (priced_shift h).runPriced_ge ((halt_shift_iff M bits tape base t).mpr halt) fuel hf

end RandomOffset

theorem SourceBounds.shiftCursor {s : BitRAMState} {n : ℕ}
    (h : SourceBounds s n) (base : ℕ) :
    SourceBounds (RandomOffset.shiftCursor base s) (base + n) := by
  have h' := h.mono (show n ≤ base + n by omega)
  refine ⟨h'.input_lower, h'.input_upper, h'.tape_lower, h'.tape_upper,
    h'.address, h'.output, ?_⟩
  change base + s.randomCursor ≤ base + n
  exact Nat.add_le_add_left h.random base

theorem SourceBounds.initial_at (base : ℕ) :
    SourceBounds {BitRAMState.initial with randomCursor := base} base := by
  simpa [RandomOffset.shiftCursor, BitRAMState.initial] using
    SourceBounds.initial.shiftCursor base

theorem sourceBounds_of_priced_at {M : BitRAM} {bits : List Bool} {tape : ℕ → Bool}
    {base n : ℕ} {s : BitRAMState}
    (h : PricedSteps (M.next bits tape) n
      {BitRAMState.initial with randomCursor := base} s) :
    SourceBounds s (base + n) :=
  (SourceBounds.initial_at base).priced h

end Maxwell.Cost.RealSimulation
