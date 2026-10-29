import Maxwell.Cost.BitRAM

/-! Finite execution segments for composing actual program blocks. A segment
need not halt; every transition is still a step of the concrete interpreter. -/

namespace Maxwell.Cost

inductive Steps {σ : Type} (next : σ → Option σ) : ℕ → σ → σ → Prop where
  | refl (s : σ) : Steps next 0 s s
  | step {n : ℕ} {s t u : σ} (h : next s = some t)
      (rest : Steps next n t u) : Steps next (n + 1) s u

namespace Steps

theorem trans {σ : Type} {next : σ → Option σ} {m n : ℕ} {s t u : σ}
    (h : Steps next m s t) (k : Steps next n t u) : Steps next (m + n) s u := by
  induction h with
  | refl s => simpa using k
  | step h rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Steps.step h (ih k))

theorem terminates {σ : Type} {next : σ → Option σ} {m n : ℕ} {s t u : σ}
    (h : Steps next m s t) (k : Terminates next n t u) :
    Terminates next (m + n) s u := by
  induction h with
  | refl s => simpa using k
  | step h rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Terminates.step h (ih k))

end Steps

theorem delay_steps {σ : Type} (next : σ → Option (PricedStep σ))
    (n : ℕ) (s : σ) :
    Steps (microNext next) (n + 1) (.delay n s) (.ready s) := by
  induction n with
  | zero => exact Steps.step rfl (Steps.refl _)
  | succ n ih => exact Steps.step rfl ih

/-- A priced instruction expands to precisely its declared number of unit
transitions; the whole charge is paid before the next instruction runs. -/
theorem priced_step_steps {σ : Type} (next : σ → Option (PricedStep σ))
    {s t : σ} {extra : ℕ} (h : next s = some ⟨t, extra⟩) :
    Steps (microNext next) (extra + 1) (.ready s) (.ready t) := by
  cases extra with
  | zero => exact Steps.step (by simp [microNext, h]) (Steps.refl _)
  | succ n => exact Steps.step (by simp [microNext, h]) (delay_steps next n t)

inductive PricedSteps {σ : Type} (next : σ → Option (PricedStep σ)) :
    ℕ → σ → σ → Prop where
  | refl (s : σ) : PricedSteps next 0 s s
  | step {n extra : ℕ} {s t u : σ} (h : next s = some ⟨t, extra⟩)
      (rest : PricedSteps next n t u) : PricedSteps next (extra + 1 + n) s u

namespace PricedSteps

theorem trans {σ : Type} {next : σ → Option (PricedStep σ)}
    {m n : ℕ} {s t u : σ} (h : PricedSteps next m s t)
    (k : PricedSteps next n t u) : PricedSteps next (m + n) s u := by
  induction h with
  | refl s => simpa using k
  | step h rest ih => simpa [Nat.add_assoc] using PricedSteps.step h (ih k)

theorem micro {σ : Type} {next : σ → Option (PricedStep σ)}
    {n : ℕ} {s t : σ} (h : PricedSteps next n s t) :
    Steps (microNext next) n (.ready s) (.ready t) := by
  induction h with
  | refl s => exact Steps.refl _
  | step h rest ih => exact (priced_step_steps next h).trans ih

theorem terminates {σ : Type} {next : σ → Option (PricedStep σ)}
    {n : ℕ} {s t : σ} (h : PricedSteps next n s t) (halt : next t = none) :
    Terminates (microNext next) n (.ready s) (.ready t) := by
  simpa using h.micro.terminates (Terminates.halt (next := microNext next)
    (MicroState.ready t) (by simp [microNext, halt]))

theorem runPriced {σ : Type} {next : σ → Option (PricedStep σ)}
    {n : ℕ} {s t : σ} (h : PricedSteps next n s t) (halt : next t = none) :
    (Cost.runPriced next (n + 1) s).finished = some t ∧
      (Cost.runPriced next (n + 1) s).instructions = n := by
  have hh := runCapped_of_terminates (microNext next) (h.terminates halt)
  constructor
  · simp only [Cost.runPriced, hh.1, Option.bind_some, MicroState.completed]
  · exact hh.2

end PricedSteps

/-- A proof convenience for fixed instruction blocks. This executes the
actual transition function and accumulates its prices; it adds no machine
instruction or host-computation shortcut. -/
def executeInstructions {σ : Type} (next : σ → Option (PricedStep σ)) :
    ℕ → σ → Option (σ × ℕ)
  | 0, s => some (s, 0)
  | n + 1, s => do
      let step ← next s
      let (t, cost) ← executeInstructions next n step.state
      pure (t, step.extra + 1 + cost)

theorem executeInstructions_sound {σ : Type} (next : σ → Option (PricedStep σ))
    {instructions cost : ℕ} {s t : σ}
    (h : executeInstructions next instructions s = some (t, cost)) :
    PricedSteps next cost s t := by
  induction instructions generalizing s cost with
  | zero =>
    simp only [executeInstructions, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact PricedSteps.refl _
  | succ instructions ih =>
    change (next s).bind (fun step =>
      (executeInstructions next instructions step.state).bind (fun result =>
        some (result.1, step.extra + 1 + result.2))) = some (t, cost) at h
    cases hs : next s with
    | none => simp [hs] at h
    | some step =>
      simp only [hs, Option.bind_some] at h
      cases hr : executeInstructions next instructions step.state with
      | none => simp [hr] at h
      | some result =>
        rcases result with ⟨u, n⟩
        simp only [hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact PricedSteps.step hs (ih hr)

/-- Fixed-count unit-step execution, useful for literal Boolean blocks. -/
def advance {σ : Type} (next : σ → Option σ) : ℕ → σ → Option σ
  | 0, s => some s
  | n + 1, s => (next s).bind (advance next n)

theorem advance_steps {σ : Type} (next : σ → Option σ) {n : ℕ} {s t : σ}
    (h : advance next n s = some t) : Steps next n s t := by
  induction n generalizing s with
  | zero =>
    simp only [advance, Option.some.injEq] at h
    subst t
    exact Steps.refl _
  | succ n ih =>
    change (next s).bind (advance next n) = some t at h
    cases hs : next s with
    | none => simp [hs] at h
    | some u =>
      simp only [hs, Option.bind_some] at h
      exact Steps.step hs (ih h)

theorem runCapped_of_terminates_ge {σ : Type} (next : σ → Option σ)
    {n : ℕ} {s t : σ} (h : Terminates next n s t) (fuel : ℕ) (hf : n + 1 ≤ fuel) :
    (runCapped next fuel s).finished = some t ∧
      (runCapped next fuel s).instructions = n := by
  induction h generalizing fuel with
  | halt s h =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [runCapped, h]
  | @step n s t u h rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hh := ih fuel (by omega)
      simp [runCapped, h, hh.1, hh.2]

theorem PricedSteps.runPriced_ge {σ : Type} {next : σ → Option (PricedStep σ)}
    {n : ℕ} {s t : σ} (h : PricedSteps next n s t) (halt : next t = none)
    (fuel : ℕ) (hf : n + 1 ≤ fuel) :
    (Cost.runPriced next fuel s).finished = some t ∧
      (Cost.runPriced next fuel s).instructions = n := by
  have hh := runCapped_of_terminates_ge (microNext next) (h.terminates halt) fuel hf
  constructor
  · simp only [Cost.runPriced, hh.1, Option.bind_some, MicroState.completed]
  · exact hh.2

theorem PricedSteps.conserved {σ α : Type} {next : σ → Option (PricedStep σ)}
    {n : ℕ} {s t : σ} (h : PricedSteps next n s t) (observable : σ → α)
    (preserved : ∀ a b extra, next a = some ⟨b, extra⟩ → observable b = observable a) :
    observable t = observable s := by
  induction h with
  | refl s => rfl
  | step h rest ih => exact ih.trans (preserved _ _ _ h)

end Maxwell.Cost
