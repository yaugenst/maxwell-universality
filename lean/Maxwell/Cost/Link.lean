import Maxwell.Cost.Execution

/-! Linking finite Boolean programs. Internal control-flow targets are
relocated; a literal halt becomes a separately charged jump to the caller's
return address. The code is never computed from a problem's answer. -/

namespace Maxwell.Cost

def BitRAMInstruction.relocate (base returnPC : ℕ) : BitRAMInstruction → BitRAMInstruction
  | .branch r yes no => .branch r (base + yes) (base + no)
  | .jump target => .jump (base + target)
  | .halt => .jump returnPC
  | instruction => instruction

def BitRAMState.relocate (base : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with pc := base + s.pc}

def BitRAM.link (preamble : List BitRAMInstruction) (body : BitRAM)
    (returnPC : ℕ) (suffix : List BitRAMInstruction) : BitRAM :=
  ⟨preamble ++ body.code.map (BitRAMInstruction.relocate preamble.length returnPC) ++ suffix⟩

theorem BitRAM.link_lookup (preamble : List BitRAMInstruction) (body : BitRAM)
    (returnPC : ℕ) (suffix : List BitRAMInstruction) (pc : ℕ) (hpc : pc < body.code.length) :
    (BitRAM.link preamble body returnPC suffix).code[preamble.length + pc]? =
      (body.code[pc]?).map (BitRAMInstruction.relocate preamble.length returnPC) := by
  simp [BitRAM.link, List.getElem?_append, hpc]

theorem BitRAM.next_code_present (body : BitRAM) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (step : PricedStep BitRAMState)
    (h : body.next input tape s = some step) : s.pc < body.code.length := by
  by_contra hpc
  have hh : body.code[s.pc]? = none := List.getElem?_eq_none (by omega)
  simp [BitRAM.next, hh] at h

/-- Every nonhalting body instruction has exactly the same price and data
effect inside the linked program. Only its control-flow addresses shift. -/
theorem BitRAM.link_next (preamble : List BitRAMInstruction) (body : BitRAM)
    (returnPC : ℕ) (suffix : List BitRAMInstruction) (input : List Bool)
    (tape : ℕ → Bool) (s t : BitRAMState) (extra : ℕ)
    (h : body.next input tape s = some ⟨t, extra⟩) :
    (BitRAM.link preamble body returnPC suffix).next input tape (s.relocate preamble.length) =
      some ⟨t.relocate preamble.length, extra⟩ := by
  have hpc := body.next_code_present input tape s ⟨t, extra⟩ h
  have hl := BitRAM.link_lookup preamble body returnPC suffix s.pc hpc
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next, hi] at h
  | some instruction =>
    cases instruction <;> simp only [BitRAM.next, hi, Option.some.injEq,
      PricedStep.mk.injEq, reduceCtorEq] at h <;> try contradiction
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [BitRAM.next, BitRAMState.relocate, hl, hi,
      BitRAMInstruction.relocate, BitRAMState.setRegister, BitRAMState.setTape,
      Nat.add_assoc]
    all_goals split <;> simp_all

theorem PricedSteps.link {body : BitRAM} {input : List Bool} {tape : ℕ → Bool}
    {n : ℕ} {s t : BitRAMState} (h : PricedSteps (body.next input tape) n s t)
    (preamble : List BitRAMInstruction) (returnPC : ℕ) (suffix : List BitRAMInstruction) :
    PricedSteps ((BitRAM.link preamble body returnPC suffix).next input tape) n
      (s.relocate preamble.length) (t.relocate preamble.length) := by
  induction h with
  | refl s => exact PricedSteps.refl _
  | step h rest ih =>
    exact PricedSteps.step (BitRAM.link_next preamble body returnPC suffix input tape _ _ _ h) ih

/-- Returning from a literal halt is an actual one-step jump, not a free
meta-level continuation. -/
theorem BitRAM.link_return (preamble : List BitRAMInstruction) (body : BitRAM)
    (returnPC : ℕ) (suffix : List BitRAMInstruction) (input : List Bool)
    (tape : ℕ → Bool) (s : BitRAMState) (h : body.code[s.pc]? = some .halt) :
    (BitRAM.link preamble body returnPC suffix).next input tape (s.relocate preamble.length) =
      some ⟨{s with pc := returnPC}, 0⟩ := by
  have hpc : s.pc < body.code.length := List.getElem?_eq_some_iff.mp h |>.1
  have hl := BitRAM.link_lookup preamble body returnPC suffix s.pc hpc
  simp [BitRAM.next, BitRAMState.relocate, hl, h, BitRAMInstruction.relocate]

/-- A fixed renaming selects distinct caller-owned work tapes without
duplicating a parser or arithmetic correctness proof. -/
def BitRAMInstruction.renameTapes (p : Equiv.Perm ℕ) :
    BitRAMInstruction → BitRAMInstruction
  | .readTape tape value present => .readTape (p tape) value present
  | .writeTape tape value => .writeTape (p tape) value
  | .eraseTape tape => .eraseTape (p tape)
  | .tapeLeft tape => .tapeLeft (p tape)
  | .tapeRight tape => .tapeRight (p tape)
  | instruction => instruction

def BitRAM.renameTapes (p : Equiv.Perm ℕ) (body : BitRAM) : BitRAM :=
  ⟨body.code.map (BitRAMInstruction.renameTapes p)⟩

def BitRAMState.renameTapes (p : Equiv.Perm ℕ) (s : BitRAMState) : BitRAMState :=
  {s with tapes := s.tapes ∘ p.symm}

theorem BitRAMState.renameTapes_setTape (p : Equiv.Perm ℕ) (s : BitRAMState)
    (i : ℕ) (t : BitTape) :
    (s.setTape i t).renameTapes p = (s.renameTapes p).setTape (p i) t := by
  simp only [BitRAMState.setTape, BitRAMState.renameTapes]
  congr 1
  simpa only [Equiv.symm_symm] using Function.update_comp_equiv s.tapes p.symm i t

/-- Tape renaming commutes with every actual interpreter step, preserving
its price. It changes neither program length nor random-bit usage. -/
theorem BitRAM.renameTapes_next (p : Equiv.Perm ℕ) (body : BitRAM)
    (input : List Bool) (randomTape : ℕ → Bool) (s : BitRAMState) :
    (body.renameTapes p).next input randomTape (s.renameTapes p) =
      (body.next input randomTape s).map (fun step =>
        ⟨step.state.renameTapes p, step.extra⟩) := by
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next, BitRAM.renameTapes, BitRAMState.renameTapes, hi]
  | some instruction =>
    cases instruction <;> simp [BitRAM.next, BitRAM.renameTapes, BitRAMState.renameTapes,
      hi, BitRAMInstruction.renameTapes, BitRAMState.setRegister, BitRAMState.setTape,
      Function.comp_def]
    all_goals first
    | rfl
    | simpa only [Equiv.symm_symm, Function.comp_def] using
        (Function.update_comp_equiv s.tapes p.symm _ _).symm

theorem PricedSteps.renameTapes {body : BitRAM} {input : List Bool}
    {randomTape : ℕ → Bool} {n : ℕ} {s t : BitRAMState}
    (h : PricedSteps (body.next input randomTape) n s t) (p : Equiv.Perm ℕ) :
    PricedSteps ((body.renameTapes p).next input randomTape) n
      (s.renameTapes p) (t.renameTapes p) := by
  induction h with
  | refl s => exact PricedSteps.refl _
  | step h rest ih =>
    apply PricedSteps.step _ ih
    rw [BitRAM.renameTapes_next, h]
    rfl

end Maxwell.Cost
