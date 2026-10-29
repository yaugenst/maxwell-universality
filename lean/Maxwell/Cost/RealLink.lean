import Maxwell.Cost.Execution

/-! Linking actual finite Real-RAM instruction lists. A subroutine's halt
becomes a charged jump; all data effects retain their original semantics. -/
namespace Maxwell.Cost

def RAMInstruction.relocate (base returnPC : ℕ) : RAMInstruction → RAMInstruction
  | .branchLE a b yes no => .branchLE a b (base + yes) (base + no)
  | .branchIndexLE a b yes no => .branchIndexLE a b (base + yes) (base + no)
  | .jump target => .jump (base + target)
  | .halt => .jump returnPC
  | instruction => instruction

def RAMState.relocate (base : ℕ) (s : RAMState) : RAMState :=
  {s with pc := base + s.pc}

/-- This certificate ranges only over the fixed finite code. -/
def Machine.Contains (outer body : Machine) (base returnPC : ℕ) : Prop :=
  ∀ i : Fin body.code.length, outer.code[base + i.val]? =
    (body.code[i.val]?).map (RAMInstruction.relocate base returnPC)

instance machineContainsDecidable (outer body : Machine) (base returnPC : ℕ) :
    Decidable (outer.Contains body base returnPC) := inferInstanceAs
  (Decidable (∀ i : Fin body.code.length, outer.code[base + i.val]? =
    (body.code[i.val]?).map (RAMInstruction.relocate base returnPC)))

theorem Machine.next_code_present (body : Machine) (input : RAMInput) (tape : ℕ → Bool)
    (s t : RAMState) (h : body.next input tape s = some t) : s.pc < body.code.length := by
  by_contra hpc
  have hh : body.code[s.pc]? = none := List.getElem?_eq_none (by omega)
  simp [Machine.next, hh] at h

theorem Machine.Contains.next {outer body : Machine} {base returnPC : ℕ}
    (hc : outer.Contains body base returnPC) (input : RAMInput) (tape : ℕ → Bool)
    {s t : RAMState} (h : body.next input tape s = some t) :
    outer.next input tape (s.relocate base) = some (t.relocate base) := by
  have hp := body.next_code_present input tape s t h
  have hl := hc ⟨s.pc, hp⟩
  cases hi : body.code[s.pc]? with
  | none => simp [Machine.next, hi] at h
  | some instruction =>
    cases instruction <;> simp only [Machine.next, hi, Option.some.injEq, reduceCtorEq] at h <;>
      try contradiction
    all_goals subst t
    all_goals simp [Machine.next, RAMState.relocate, hl, hi,
      RAMInstruction.relocate, RAMState.setWord, RAMState.setIndex, Nat.add_assoc]
    all_goals split <;> simp_all [not_le_of_gt]

theorem Machine.Contains.steps {outer body : Machine} {base returnPC : ℕ}
    (hc : outer.Contains body base returnPC) (input : RAMInput) (tape : ℕ → Bool)
    {s t : RAMState} {cost : ℕ} (h : Steps (body.next input tape) cost s t) :
    Steps (outer.next input tape) cost (s.relocate base) (t.relocate base) := by
  induction h with
  | refl s => exact Steps.refl _
  | step h rest ih => exact Steps.step (hc.next input tape h) ih

theorem Machine.Contains.return_step {outer body : Machine} {base returnPC : ℕ}
    (hc : outer.Contains body base returnPC) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (h : body.code[s.pc]? = some .halt) :
    outer.next input tape (s.relocate base) = some {s with pc := returnPC} := by
  have hp := (List.getElem?_eq_some_iff.mp h).1
  have heq := hc ⟨s.pc, hp⟩
  simp [Machine.next, RAMState.relocate, heq, h, RAMInstruction.relocate]

theorem Machine.Contains.call {outer body : Machine} {base returnPC : ℕ}
    (hc : outer.Contains body base returnPC) (input : RAMInput) (tape : ℕ → Bool)
    {s t : RAMState} {cost : ℕ} (h : Steps (body.next input tape) cost s t)
    (halt : body.code[t.pc]? = some .halt) :
    Steps (outer.next input tape) (cost + 1) (s.relocate base) {t with pc := returnPC} := by
  exact (hc.steps input tape h).trans
    (Steps.step (hc.return_step input tape t halt) (Steps.refl _))

theorem Machine.Contains.call_at {outer body : Machine} {base returnPC cost : ℕ}
    (hc : outer.Contains body base returnPC) (input : RAMInput) (tape : ℕ → Bool)
    (s t : RAMState) (hpc : s.pc = base)
    (hsteps : Steps (body.next input tape) cost {s with pc := 0} t)
    (hhalt : body.code[t.pc]? = some .halt) :
    Steps (outer.next input tape) (cost + 1) s {t with pc := returnPC} := by
  have h := hc.call input tape hsteps hhalt
  have hid : ({s with pc := 0} : RAMState).relocate base = s := by
    simp [RAMState.relocate, ← hpc]
  simpa only [hid] using h

theorem Terminates.toSteps {σ : Type} {next : σ → Option σ} {n : ℕ} {s t : σ}
    (h : Terminates next n s t) : Steps next n s t := by
  induction h with
  | halt s _ => exact Steps.refl s
  | step h _ ih => exact Steps.step h ih

end Maxwell.Cost
