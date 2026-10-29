import Maxwell.Cost.Structured.Hoare

/-! Least-success search compiled to one fixed loop. The predicate is a
specification: each test and update must be justified by an execution of
the supplied finite code, with all body and branch charges retained. -/
namespace Maxwell.Cost.SelectedParameters.LeastLoop
open Structured

def code (flag : ℕ) (test advance : Code) : Code :=
  .seq test (.loop flag (.seq advance test))

theorem tail (P : ℕ → Prop) [DecidablePred P] (existsP : ∃ n, P n)
    (flag : ℕ) (test advance : Code) (testCost advanceCost : ℕ)
    (input : List Bool) (randomTape : ℕ → Bool) (R : ℕ → Store → Prop)
    (htest : ∀ n, n ≤ Nat.find existsP → ∀ s, R n s →
      ∃ cost t, Executes input randomTape test cost s t ∧ cost ≤ testCost ∧
        R n t ∧ t.val.registers flag = decide (¬P n))
    (hadvance : ∀ n, n < Nat.find existsP → ∀ s, R n s →
      ∃ cost t, Executes input randomTape advance cost s t ∧ cost ≤ advanceCost ∧ R (n+1) t)
    (remaining n : ℕ) (hn : n+remaining=Nat.find existsP) (s : Store)
    (hs : R n s) (hflag : s.val.registers flag = decide (¬P n)) :
    ∃ cost t, Executes input randomTape (.loop flag (.seq advance test)) cost s t ∧
      cost ≤ 1+remaining*(advanceCost+testCost+1) ∧ R (Nat.find existsP) t := by
  induction remaining generalizing n s with
  | zero =>
    have he : n=Nat.find existsP := by omega
    subst n
    have hf : s.val.registers flag = false := by simpa [Nat.find_spec existsP] using hflag
    exact ⟨1,s,.done hf,by simp,hs⟩
  | succ r ih =>
    have hlt : n<Nat.find existsP := by omega
    have hf : s.val.registers flag = true := by
      simpa [Nat.find_min existsP hlt] using hflag
    obtain ⟨c1,u,e1,p1,h1⟩ := hadvance n hlt s hs
    obtain ⟨c2,v,e2,p2,h2,g2⟩ := htest (n+1) (by omega) u h1
    obtain ⟨c3,t,e3,p3,h3⟩ := ih (n+1) (by omega) v h2 g2
    refine ⟨1+(c1+c2)+c3,t,.more hf (e1.seq e2) e3,?_,h3⟩
    rw [Nat.succ_mul]
    omega

/-- The loop returns exactly the first successful index, including zero;
there is no externally supplied iteration count in the executable code. -/
theorem executes (P : ℕ → Prop) [DecidablePred P] (existsP : ∃ n, P n)
    (flag : ℕ) (test advance : Code) (testCost advanceCost : ℕ)
    (input : List Bool) (randomTape : ℕ → Bool) (R : ℕ → Store → Prop)
    (htest : ∀ n, n ≤ Nat.find existsP → ∀ s, R n s →
      ∃ cost t, Executes input randomTape test cost s t ∧ cost ≤ testCost ∧
        R n t ∧ t.val.registers flag = decide (¬P n))
    (hadvance : ∀ n, n < Nat.find existsP → ∀ s, R n s →
      ∃ cost t, Executes input randomTape advance cost s t ∧ cost ≤ advanceCost ∧ R (n+1) t)
    (s : Store) (hs : R 0 s) :
    ∃ cost t, Executes input randomTape (code flag test advance) cost s t ∧
      cost ≤ testCost+1+Nat.find existsP*(advanceCost+testCost+1) ∧ R (Nat.find existsP) t := by
  obtain ⟨c1,u,e1,p1,h1,g1⟩ := htest 0 (Nat.zero_le _) s hs
  obtain ⟨c2,t,e2,p2,h2⟩ := tail P existsP flag test advance testCost advanceCost input randomTape R
    htest hadvance (Nat.find existsP) 0 (by omega) u h1 g1
  exact ⟨c1+c2,t,e1.seq e2,by omega,h2⟩

end Maxwell.Cost.SelectedParameters.LeastLoop
