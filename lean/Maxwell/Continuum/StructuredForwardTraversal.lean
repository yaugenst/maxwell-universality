import Maxwell.Continuum.RationalDataflowSizedCounted

/-! An ascending logical traversal implemented by an actual stored
countdown. The invariant records the number of entries already processed. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem forward_counted_executes (port : ℕ) (origin : ℤ) (body : Code)
    (input : List Bool) (tape : ℕ→Bool) (n wordLength stepCost : ℕ)
    (invariant : ℕ→Store→Prop)
    (stable : ∀j s t,CountedShifted.Frame port s t → invariant j s → invariant j t)
    (step : ∀j<n,∀xs s,invariant j s →
      s.val.tapes port=BitTape.shifted xs origin → xs.length=wordLength →
      ∃cost t,Executes input tape body cost s t ∧ invariant (j+1) t ∧
        t.val.tapes port=BitTape.shifted xs origin ∧ cost ≤ stepCost)
    (xs : List Bool) (s : Store) (hx : addressValue xs=n)
    (hword : s.val.tapes port=BitTape.shifted xs origin) (hlen : xs.length=wordLength)
    (hs : invariant 0 s) :
    ∃cost t finalWord,Executes input tape (countedProgram port body) cost s t ∧
      invariant n t ∧ t.val.tapes port=BitTape.shifted finalWord origin ∧
      finalWord.length=wordLength ∧ cost ≤ (n+1)*(13*wordLength+15)+n*stepCost := by
  let inv : ℕ→Store→Prop := fun r s => r ≤ n ∧ invariant (n-r) s
  have stable' : ∀r s t,CountedShifted.Frame port s t → inv r s → inv r t := by
    intro r s t f h
    exact ⟨h.1,stable _ s t f h.2⟩
  have step' : ∀r ys s,inv (r+1) s → s.val.tapes port=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=wordLength →
      ∃cost t,Executes input tape body cost s t ∧ inv r t ∧
        t.val.tapes port=BitTape.shifted ys origin ∧ cost ≤ stepCost := by
    intro r ys s h hw _ hl
    have hlt : n-(r+1)<n := by have := h.1;omega
    obtain ⟨c,t,e,ht,word,cost⟩ := step (n-(r+1)) hlt ys s h.2 hw hl
    have he : n-(r+1)+1=n-r := by have := h.1;omega
    rw [he] at ht
    exact ⟨c,t,e,⟨by have := h.1;omega,ht⟩,word,cost⟩
  obtain ⟨c,t,ys,e,ht,word,length,_,cost⟩ := counted_executes_sized port origin body input tape
    wordLength inv (fun _ => stepCost) stable' step' n xs s hx hword hlen
    ⟨le_rfl,by simpa using hs⟩
  refine ⟨c,t,ys,e,?_,word,length,?_⟩
  · simpa only [Nat.sub_zero] using ht.2
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using cost

#print axioms forward_counted_executes
end Maxwell.Continuum.RationalDataflow
