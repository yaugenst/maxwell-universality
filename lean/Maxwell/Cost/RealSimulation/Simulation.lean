import Maxwell.Cost.RealSimulation.InstructionSimulation
import Maxwell.Cost.RealSimulation.Dispatch
import Maxwell.Cost.RealSimulation.SourceBounds

namespace Maxwell.Cost.RealSimulation

open Control

def dispatchConstant (M : BitRAM) : ℕ :=
  instructionConstant (footprint M.code) + 3 * (M.code.length + 1)
def terminalConstant (M : BitRAM) : ℕ := 3 * (M.code.length + 1) + 2

theorem dispatch_next (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {source next : BitRAMState} {extra : ℕ}
    (hnext : M.next bits tape source = some ⟨next, extra⟩)
    (s : Store) (h : Ready (footprint M.code) origin center bits source s)
    (hinput : -(center : ℤ) < source.inputHead)
    (htapes : ∀ t, -(center : ℤ) < (source.tapes t).head) :
    ∃ cost t, cost ≤ dispatchConstant M * (extra + 1) ∧
      Executes input tape (dispatch (footprint M.code) Address.code 0 M.code) cost s t ∧
      Ready (footprint M.code) origin center bits next t := by
  cases hc : M.code[source.pc]? with
  | none => simp [BitRAM.next, hc] at hnext
  | some op =>
    obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hc
    have hf := footprint_get_fits M.code source.pc op hc
    have hs : ∀ u v, Ready (footprint M.code) origin center bits source u →
        Ready (footprint M.code) origin center bits source (u.put dispatchRegister v) := by
      intro u v hu
      exact hu.put_scratch _ _ (by decide) (by decide) (by decide) (by decide)
    obtain ⟨cost, t, hb, ht, hr⟩ := dispatch_selected (footprint M.code) Address.code input tape
      M.code 0 source.pc hj (Ready (footprint M.code) origin center bits source)
      (Ready (footprint M.code) origin center bits next) hs
      (instructionConstant (footprint M.code) * (extra + 1)) s h (by simpa using h.pc)
      (by
        intro u hu
        rw [he]
        exact instruction_next M input tape op hc hf hnext u hu hinput (fun t _ => htapes t))
    refine ⟨cost, t, ?_, ht, hr⟩
    unfold dispatchConstant
    nlinarith

theorem source_halt_code (M : BitRAM) (bits : List Bool) (tape : ℕ → Bool)
    (source : BitRAMState) (h : M.next bits tape source = none) :
    M.code[source.pc]? = none ∨ M.code[source.pc]? = some .halt := by
  cases hc : M.code[source.pc]? with
  | none => exact Or.inl rfl
  | some op =>
    cases op <;> simp only [BitRAM.next, hc, reduceCtorEq] at h
    exact Or.inr rfl

theorem interpreter_terminal (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {source : BitRAMState}
    (halt : M.next bits tape source = none)
    (s : Store) (h : Ready (footprint M.code) origin center bits source s) :
    ∃ cost t, cost ≤ terminalConstant M ∧
      Executes input tape (interpreter (footprint M.code) Address.code M) cost s t ∧
      Represents (footprint M.code) origin center bits source t.val := by
  have hh := source_halt_code M bits tape source halt
  rw [← h.pc] at hh
  obtain ⟨cost, t, hc, he, _, hf⟩ := interpreter_finish (footprint M.code) Address.code M
    input tape s h.one h.active hh
  refine ⟨cost, t, hc, he, h.toRepresents.congr ?_ hf.randomCursor⟩
  intro j hj
  exact hf.indices j (by unfold activeRegister; omega) (by unfold dispatchRegister; omega)

/-- The head center is the actual source cap. Every step is simulated before
the cap is exhausted, so subtraction never truncates a represented head. -/
theorem interpreter_priced (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {a b : BitRAMState} {n : ℕ}
    (source : PricedSteps (M.next bits tape) n a b) (halt : M.next bits tape b = none)
    (used : ℕ) (bounds : SourceBounds a used) (cap : used + n ≤ center)
    (s : Store) (hs : Ready (footprint M.code) origin center bits a s) :
    ∃ cost t, cost ≤ (dispatchConstant M + 1) * n + terminalConstant M ∧
      Executes input tape (interpreter (footprint M.code) Address.code M) cost s t ∧
      Represents (footprint M.code) origin center bits b t.val := by
  induction source generalizing used s with
  | refl a => simpa using interpreter_terminal M input tape halt s hs
  | @step n extra a b c hnext rest ih =>
    have hu : used < center := by omega
    obtain ⟨cost, t, hc, he, ht⟩ := dispatch_next M input tape hnext s hs
      (bounds.input_before_cap hu) (fun t => bounds.tape_before_cap hu t)
    have hb : SourceBounds b (used + (extra + 1)) :=
      (bounds.step hnext).mono (by omega)
    obtain ⟨restCost, u, hr, er, hf⟩ := ih halt (used + (extra + 1)) hb (by omega) t ht
    refine ⟨1 + cost + restCost, u, ?_, ?_, hf⟩
    · nlinarith
    · exact Executes.more (by rw [hs.one, hs.active]) he er

/-- A fixed finite machine implements the entire interpreter. This theorem
starts after the caller's explicit initialization prefix and records the
actual final halt, output buffer, consumed randomness, and every source cell. -/
theorem interpreter_terminates (M : BitRAM) (input : RAMInput) (tape : ℕ → Bool)
    {origin center : ℕ} {bits : List Bool} {b : BitRAMState} {n : ℕ}
    (source : PricedSteps (M.next bits tape) n BitRAMState.initial b)
    (halt : M.next bits tape b = none) (cap : n ≤ center)
    (s : Store) (hs : Ready (footprint M.code) origin center bits BitRAMState.initial s) :
    ∃ cost t, cost ≤ (dispatchConstant M + 1) * n + terminalConstant M ∧
      Terminates ((interpreter (footprint M.code) Address.code M).compile.next input tape)
        cost s.val t ∧ Represents (footprint M.code) origin center bits b t := by
  obtain ⟨cost, t, hc, he, hr⟩ := interpreter_priced M input tape source halt
    0 SourceBounds.initial (by simpa using cap) s hs
  refine ⟨cost, t.place (interpreter (footprint M.code) Address.code M).size, hc,
    he.compiled_steps.terminates (Terminates.halt _ ?_),
    hr.congr (fun _ _ => rfl) rfl⟩
  simp [Machine.next, Store.place, Code.compile_halt]

end Maxwell.Cost.RealSimulation
