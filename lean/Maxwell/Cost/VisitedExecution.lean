import Maxwell.Cost.Blocks

/-! Predicate-carrying actual execution traces. These proof objects retain
all charged transitions and certify intermediate states, not just endpoints. -/
namespace Maxwell.Cost

inductive VisitedPriced {σ : Type} (next : σ → Option (PricedStep σ)) (P : σ → Prop) :
    ℕ → σ → σ → Prop where
  | refl {s : σ} (holds : P s) : VisitedPriced next P 0 s s
  | step {n extra : ℕ} {s t u : σ} (holds : P s) (transition : next s = some ⟨t,extra⟩)
      (rest : VisitedPriced next P n t u) : VisitedPriced next P (extra+1+n) s u

namespace VisitedPriced
variable {σ : Type} {next : σ → Option (PricedStep σ)} {P Q : σ → Prop}

theorem steps {n : ℕ} {s t : σ} (h : VisitedPriced next P n s t) : PricedSteps next n s t := by
  induction h with
  | refl => exact .refl _
  | step _ hn _ ih => exact .step hn ih

theorem start {n : ℕ} {s t : σ} (h : VisitedPriced next P n s t) : P s := by
  cases h <;> assumption

theorem finish {n : ℕ} {s t : σ} (h : VisitedPriced next P n s t) : P t := by
  induction h <;> assumption

theorem mono {n : ℕ} {s t : σ} (h : VisitedPriced next P n s t) (imp : ∀ u,P u→Q u) :
    VisitedPriced next Q n s t := by
  induction h with
  | refl hs => exact .refl (imp _ hs)
  | step hs hn _ ih => exact .step (imp _ hs) hn ih

theorem trans {n m : ℕ} {s t u : σ}
    (h : VisitedPriced next P n s t) (k : VisitedPriced next P m t u) :
    VisitedPriced next P (n+m) s u := by
  induction h with
  | refl => simpa using k
  | step hs hn _ ih => simpa only [Nat.add_assoc] using VisitedPriced.step hs hn (ih k)

theorem prefix_bound {n k : ℕ} {s t u : σ} (h : VisitedPriced next P n s t)
    (hk : k≤n) (hp : PricedSteps next k s u) : P u := by
  induction h generalizing k u with
  | refl hs =>
    cases hp with
    | refl => exact hs
    | step _ _ => omega
  | @step n extra s t v hs hn rest ih =>
    cases hp with
    | refl => exact hs
    | @step k extra' _ w _ hw tail =>
      have he := Option.some.inj (hw.symm.trans hn)
      cases he
      exact ih (by omega) tail

/-- Relocation changes only the program counter; the state predicate is
transported explicitly along the same concrete interpreter transitions. -/
theorem map {τ : Type} {next' : τ → Option (PricedStep τ)} {Q : τ → Prop}
    (f : σ→τ) (preserves : ∀ s t extra,next s=some ⟨t,extra⟩→next' (f s)=some ⟨f t,extra⟩)
    (predicate : ∀ s,P s→Q (f s)) {n : ℕ} {s t : σ} (h : VisitedPriced next P n s t) :
    VisitedPriced next' Q n (f s) (f t) := by
  induction h with
  | refl hs => exact .refl (predicate _ hs)
  | step hs hn _ ih => exact .step (predicate _ hs) (preserves _ _ _ hn) ih

end VisitedPriced

/-- A finite-block proof checker. Its tests are proof obligations about the
existing interpreter; it is not a new machine instruction. -/
def checkedInstructions {σ : Type} (next : σ → Option (PricedStep σ))
    (P : σ→Prop) [DecidablePred P] : ℕ→σ→Option (σ×ℕ)
  | 0,s => if P s then some (s,0) else none
  | n+1,s => if P s then do
      let step ← next s
      let (t,cost) ← checkedInstructions next P n step.state
      pure (t,step.extra+1+cost)
    else none

theorem checkedInstructions_sound {σ : Type} (next : σ→Option (PricedStep σ))
    (P : σ→Prop) [DecidablePred P] {instructions cost : ℕ} {s t : σ}
    (h : checkedInstructions next P instructions s=some (t,cost)) :
    VisitedPriced next P cost s t := by
  induction instructions generalizing cost s with
  | zero =>
    simp only [checkedInstructions] at h
    split at h
    · simp only [Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact .refl ‹P s›
    · contradiction
  | succ n ih =>
    simp only [checkedInstructions] at h
    split at h
    · rename_i hs
      change (next s).bind (fun step =>
        (checkedInstructions next P n step.state).bind (fun result =>
          some (result.1,step.extra+1+result.2)))=some (t,cost) at h
      cases hn : next s with
      | none => simp [hn] at h
      | some step =>
        simp only [hn,Option.bind_some] at h
        cases hr : checkedInstructions next P n step.state with
        | none => simp [hr] at h
        | some result =>
          rcases result with ⟨u,m⟩
          simp only [hr,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          exact .step hs hn (ih hr)
    · contradiction

end Maxwell.Cost
