import Maxwell.Cost.SelectedParameters.LeastLoop

/-! Preserve the output certificate of the final executed test. The advance
step needs only the loop invariant; no final-result premise is imposed before
the successful test has run. -/
namespace Maxwell.Cost.SelectedParameters.LeastLoop
open Structured

theorem tail_result (P : ℕ→Prop) [DecidablePred P] (existsP : ∃n,P n)
    (flag : ℕ) (test advance : Code) (testCost advanceCost : ℕ)
    (input : List Bool) (tape : ℕ→Bool) (R Q : ℕ→Store→Prop)
    (htest : ∀n,n ≤ Nat.find existsP→∀s,R n s→∃cost t,
      Executes input tape test cost s t ∧ cost ≤ testCost ∧ R n t ∧ Q n t ∧
      t.val.registers flag=decide (¬P n))
    (hadvance : ∀n,n < Nat.find existsP→∀s,R n s→∃cost t,
      Executes input tape advance cost s t ∧ cost ≤ advanceCost ∧ R (n+1) t)
    (remaining n : ℕ) (hn : n+remaining=Nat.find existsP) (s : Store)
    (hs : R n s) (hq : Q n s) (hflag : s.val.registers flag=decide (¬P n)) :
    ∃cost t,Executes input tape (.loop flag (.seq advance test)) cost s t ∧
      cost ≤ 1+remaining*(advanceCost+testCost+1) ∧ R (Nat.find existsP) t ∧ Q (Nat.find existsP) t := by
  induction remaining generalizing n s with
  | zero =>
    have he : n=Nat.find existsP := by omega
    subst n
    have hf : s.val.registers flag=false := by simpa [Nat.find_spec existsP] using hflag
    exact ⟨1,s,.done hf,by simp,hs,hq⟩
  | succ r ih =>
    have hlt : n < Nat.find existsP := by omega
    have hf : s.val.registers flag=true := by simpa [Nat.find_min existsP hlt] using hflag
    obtain ⟨c1,u,e1,p1,h1⟩ := hadvance n hlt s hs
    obtain ⟨c2,v,e2,p2,h2,q2,g2⟩ := htest (n+1) (by omega) u h1
    obtain ⟨c3,t,e3,p3,h3,q3⟩ := ih (n+1) (by omega) v h2 q2 g2
    refine ⟨1+(c1+c2)+c3,t,.more hf (e1.seq e2) e3,?_,h3,q3⟩
    rw [Nat.succ_mul]
    omega

theorem executes_result (P : ℕ→Prop) [DecidablePred P] (existsP : ∃n,P n)
    (flag : ℕ) (test advance : Code) (testCost advanceCost : ℕ)
    (input : List Bool) (tape : ℕ→Bool) (R Q : ℕ→Store→Prop)
    (htest : ∀n,n ≤ Nat.find existsP→∀s,R n s→∃cost t,
      Executes input tape test cost s t ∧ cost ≤ testCost ∧ R n t ∧ Q n t ∧
      t.val.registers flag=decide (¬P n))
    (hadvance : ∀n,n < Nat.find existsP→∀s,R n s→∃cost t,
      Executes input tape advance cost s t ∧ cost ≤ advanceCost ∧ R (n+1) t)
    (s : Store) (hs : R 0 s) :
    ∃cost t,Executes input tape (code flag test advance) cost s t ∧
      cost ≤ testCost+1+Nat.find existsP*(advanceCost+testCost+1) ∧
      R (Nat.find existsP) t ∧ Q (Nat.find existsP) t := by
  obtain ⟨c1,u,e1,p1,h1,q1,g1⟩ := htest 0 (Nat.zero_le _) s hs
  obtain ⟨c2,t,e2,p2,h2,q2⟩ := tail_result P existsP flag test advance testCost advanceCost input tape R Q
    htest hadvance (Nat.find existsP) 0 (by omega) u h1 q1 g1
  exact ⟨c1+c2,t,e1.seq e2,by omega,h2,q2⟩

#print axioms executes_result
end Maxwell.Cost.SelectedParameters.LeastLoop
