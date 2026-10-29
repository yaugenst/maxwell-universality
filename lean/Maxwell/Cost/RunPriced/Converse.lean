import Maxwell.Cost.Execution

namespace Maxwell.Cost

def MicroState.remainingCharge {σ : Type} : MicroState σ → ℕ
  | .ready _ => 0
  | .delay n _ => n+1

/-- A terminating micro-execution pays all remaining delay before its
priced execution starts. No part of an address charge can be discarded. -/
theorem micro_terminates_priced {σ : Type} {next : σ → Option (PricedStep σ)}
    {n : ℕ} {s t : MicroState σ} (h : Terminates (microNext next) n s t) :
    ∃ cost, n = s.remainingCharge + cost ∧
      PricedSteps next cost s.state t.state ∧ next t.state = none := by
  induction h with
  | halt s hs =>
    cases s with
    | ready s =>
      refine ⟨0, rfl, PricedSteps.refl s, ?_⟩
      cases hn : next s with
      | none => exact hn
      | some step =>
        rcases step with ⟨u, extra⟩
        cases extra <;> simp [microNext, hn] at hs
    | delay k s => cases k <;> simp [microNext] at hs
  | @step n s middle t hs rest ih =>
    obtain ⟨cost, hc, hp, ht⟩ := ih
    cases s with
    | ready s =>
      cases hn : next s with
      | none => simp [microNext, hn] at hs
      | some step =>
        rcases step with ⟨u, extra⟩
        cases extra with
        | zero =>
          simp only [microNext, hn, Option.some.injEq] at hs
          subst middle
          refine ⟨1+cost, ?_, PricedSteps.step hn hp, ht⟩
          simp only [MicroState.remainingCharge] at hc ⊢
          omega
        | succ k =>
          simp only [microNext, hn, Option.some.injEq] at hs
          subst middle
          refine ⟨k+1+1+cost, ?_, PricedSteps.step hn hp, ht⟩
          simp only [MicroState.remainingCharge] at hc ⊢
          omega
    | delay k s =>
      cases k with
      | zero =>
        simp only [microNext, Option.some.injEq] at hs
        subst middle
        refine ⟨cost, ?_, hp, ht⟩
        simp only [MicroState.remainingCharge] at hc ⊢
        omega
      | succ k =>
        simp only [microNext, Option.some.injEq] at hs
        subst middle
        refine ⟨cost, ?_, hp, ht⟩
        simp only [MicroState.remainingCharge] at hc ⊢
        omega

/-- Successful capped execution yields its exact priced instruction
segment and a halted final state. This is the converse of `PricedSteps.runPriced_ge`. -/
theorem runPriced_pricedSteps {σ : Type} (next : σ → Option (PricedStep σ))
    (fuel : ℕ) (s t : σ) (h : (runPriced next fuel s).finished = some t) :
    PricedSteps next (runPriced next fuel s).instructions s t ∧ next t = none := by
  obtain ⟨cost, hc, hp, ht⟩ := micro_terminates_priced (runPriced_sound next fuel s t h)
  simp only [MicroState.remainingCharge, Nat.zero_add, MicroState.state] at hc hp ht
  exact ⟨hc ▸ hp, ht⟩

end Maxwell.Cost
