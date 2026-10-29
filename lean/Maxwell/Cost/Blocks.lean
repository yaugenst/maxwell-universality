import Maxwell.Cost.Link

namespace Maxwell.Cost

/-- A finite, decidable certificate that a literal program contains one
relocated subroutine. The index ranges over code, never over input data. -/
def BitRAM.Contains (outer body : BitRAM) (base returnPC : ℕ) : Prop :=
  ∀ i : Fin body.code.length,
    outer.code[base + i.val]? =
      (body.code[i.val]?).map (BitRAMInstruction.relocate base returnPC)

instance (outer body : BitRAM) (base returnPC : ℕ) :
    Decidable (outer.Contains body base returnPC) := inferInstanceAs
  (Decidable (∀ i : Fin body.code.length,
    outer.code[base + i.val]? =
      (body.code[i.val]?).map (BitRAMInstruction.relocate base returnPC)))

theorem BitRAM.Contains.next {outer body : BitRAM} {base returnPC : ℕ}
    (hc : outer.Contains body base returnPC) (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {extra : ℕ}
    (h : body.next input tape s = some ⟨t, extra⟩) :
    outer.next input tape (s.relocate base) = some ⟨t.relocate base, extra⟩ := by
  have hp := body.next_code_present input tape s ⟨t, extra⟩ h
  have hl := BitRAM.link_next (List.replicate base .halt) body returnPC [] input tape s t extra h
  have heq := hc ⟨s.pc, hp⟩
  have hlookup := BitRAM.link_lookup (List.replicate base .halt) body returnPC [] s.pc hp
  simp only [List.length_replicate] at hl hlookup
  change outer.code[base + s.pc]? = _ at heq
  simp only [BitRAM.next, BitRAMState.relocate] at hl ⊢
  simpa only [heq, hlookup] using hl

theorem BitRAM.Contains.steps {outer body : BitRAM} {base returnPC : ℕ}
    (hc : outer.Contains body base returnPC) (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ}
    (h : PricedSteps (body.next input tape) cost s t) :
    PricedSteps (outer.next input tape) cost (s.relocate base) (t.relocate base) := by
  induction h with
  | refl s => exact PricedSteps.refl _
  | step h rest ih => exact PricedSteps.step (hc.next input tape h) ih

theorem BitRAM.Contains.return_step {outer body : BitRAM} {base returnPC : ℕ}
    (hc : outer.Contains body base returnPC) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (h : body.code[s.pc]? = some .halt) :
    outer.next input tape (s.relocate base) = some ⟨{s with pc := returnPC}, 0⟩ := by
  have hp := (List.getElem?_eq_some_iff.mp h).1
  have heq := hc ⟨s.pc, hp⟩
  simp [BitRAM.next, BitRAMState.relocate, heq, h, BitRAMInstruction.relocate]

/-- A subroutine return is charged and executed, so block composition does
not silently treat host-language continuation as a machine instruction. -/
theorem BitRAM.Contains.call {outer body : BitRAM} {base returnPC : ℕ}
    (hc : outer.Contains body base returnPC) (input : List Bool) (tape : ℕ → Bool)
    {s t : BitRAMState} {cost : ℕ}
    (h : PricedSteps (body.next input tape) cost s t)
    (halt : body.code[t.pc]? = some .halt) :
    PricedSteps (outer.next input tape) (cost + 1) (s.relocate base) {t with pc := returnPC} := by
  exact (hc.steps input tape h).trans
    (PricedSteps.step (hc.return_step input tape t halt) (PricedSteps.refl _))

/-- Caller-state form of a linked call; only its program counter is reset
when invoking the local correctness theorem. -/
theorem BitRAM.Contains.call_at {outer body : BitRAM} {base returnPC cost : ℕ}
    (hc : outer.Contains body base returnPC) (input : List Bool) (tape : ℕ → Bool)
    (s t : BitRAMState) (hpc : s.pc = base)
    (hsteps : PricedSteps (body.next input tape) cost {s with pc := 0} t)
    (hhalt : body.code[t.pc]? = some .halt) :
    PricedSteps (outer.next input tape) (cost + 1) s {t with pc := returnPC} := by
  have h := hc.call input tape hsteps hhalt
  have hid : ({s with pc := 0} : BitRAMState).relocate base = s := by
    simp [BitRAMState.relocate, ← hpc]
  simpa only [hid] using h

end Maxwell.Cost
