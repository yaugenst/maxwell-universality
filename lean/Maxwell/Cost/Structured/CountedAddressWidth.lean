import Maxwell.Cost.Structured.CountedShifted
import Maxwell.Cost.Structured.AddressWidth

namespace Maxwell.Cost.Structured.CountedShifted
open scoped BigOperators

/-- Checked countdown semantics, keeping the initial test separate so the
induction can compose the actual loop backedge without a host continuation. -/
private theorem visited_parts (W countTape : ℕ) (origin : ℤ) (body : Code)
    (input : List Bool) (tape : ℕ→Bool) (invariant : ℕ→Store→Prop) (bound : ℕ→ℕ)
    (stable : ∀ n s t, Frame countTape s t → invariant n s → invariant n t)
    (bodyCorrect : ∀ n xs s, Address.Within W s.val → invariant (n+1) s →
      s.val.tapes countTape=BitTape.shifted xs origin → addressValue xs=n →
      ∃ bodyCost t, Visited W input tape body bodyCost s t ∧
        invariant n t ∧ t.val.tapes countTape=BitTape.shifted xs origin ∧ bodyCost ≤ bound n)
    (n : ℕ) (xs : List Bool) (s : Store) (hvalue : addressValue xs=n)
    (hword : s.val.tapes countTape=BitTape.shifted xs origin)
    (hinvariant : invariant n s) (hs : Address.Within W s.val) :
    ∃ tested loopCost t finalWord,
      Visited W input tape (test countTape) (13*xs.length+14) s tested ∧
      Visited W input tape (.loop 29 (.seq body (test countTape))) loopCost tested t ∧
      invariant 0 t ∧ t.val.tapes countTape=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧ t.val.registers 29=false ∧
      13*xs.length+14+loopCost ≤ (n+1)*(13*xs.length+15)+∑ k ∈ Finset.range n, bound k := by
  induction n generalizing xs s with
  | zero =>
    obtain ⟨t,ht,hw,hz,hf⟩ := test_executes countTape origin input tape s xs hword
    have ht' := ht.visited_noAddressPush (show (test countTape).noAddressPush=true from rfl) hs
    have hfalse := hz.mpr hvalue
    refine ⟨t,1,t,subtractBit true xs,ht',.done hfalse ht'.finish,
      stable 0 s t hf hinvariant,hw,subtractBit_length true xs,hfalse,?_⟩
    simp
  | succ n ih =>
    obtain ⟨tested,htest,hw,hz,hf⟩ := test_executes countTape origin input tape s xs hword
    have ht := htest.visited_noAddressPush (show (test countTape).noAddressPush=true from rfl) hs
    have hpositive : 0<addressValue xs := by omega
    have hdecrease : addressValue (subtractBit true xs)=n := by
      rw [subtractBit_pred xs hpositive,hvalue]
      omega
    have htrue : tested.val.registers 29=true := by
      cases hb : tested.val.registers 29 with
      | true => rfl
      | false => have := hz.mp hb; omega
    obtain ⟨bodyCost,middle,hbody,hmInv,hmWord,hmCost⟩ :=
      bodyCorrect n (subtractBit true xs) tested ht.finish
        (stable (n+1) s tested hf hinvariant) hw hdecrease
    obtain ⟨afterTest,restCost,t,finalWord,restTest,restLoop,htInv,htWord,htLen,htFalse,htCost⟩ :=
      ih (subtractBit true xs) middle hdecrease hmWord hmInv hbody.finish
    refine ⟨tested,_,t,finalWord,ht,.more htrue (hbody.seq restTest) restLoop,
      htInv,htWord,htLen.trans (subtractBit_length true xs),htFalse,?_⟩
    simp only [subtractBit_length] at htCost ⊢
    rw [Finset.sum_range_succ]
    nlinarith

/-- A genuine counted loop whose existing storage invariant is augmented
by a checked address-width contract for its fixed body. All counter tests,
return jumps, and loop backedges remain in the exact charged execution. -/
theorem executes_visited (W countTape : ℕ) (origin : ℤ) (body : Code)
    (input : List Bool) (tape : ℕ→Bool) (invariant : ℕ→Store→Prop) (bound : ℕ→ℕ)
    (stable : ∀ n s t, Frame countTape s t → invariant n s → invariant n t)
    (bodyCorrect : ∀ n xs s, Address.Within W s.val → invariant (n+1) s →
      s.val.tapes countTape=BitTape.shifted xs origin → addressValue xs=n →
      ∃ bodyCost t, Visited W input tape body bodyCost s t ∧
        invariant n t ∧ t.val.tapes countTape=BitTape.shifted xs origin ∧ bodyCost ≤ bound n)
    (n : ℕ) (xs : List Bool) (s : Store) (hvalue : addressValue xs=n)
    (hword : s.val.tapes countTape=BitTape.shifted xs origin)
    (hinvariant : invariant n s) (hs : Address.Within W s.val) :
    ∃ cost t finalWord, Visited W input tape (code countTape body) cost s t ∧
      invariant 0 t ∧ t.val.tapes countTape=BitTape.shifted finalWord origin ∧
      finalWord.length=xs.length ∧ t.val.registers 29=false ∧
      cost ≤ (n+1)*(13*xs.length+15)+∑ k ∈ Finset.range n, bound k := by
  obtain ⟨tested,cost,t,finalWord,htest,hloop,hinv,hword,hlen,hfalse,hcost⟩ :=
    visited_parts W countTape origin body input tape invariant bound stable bodyCorrect
      n xs s hvalue hword hinvariant hs
  exact ⟨_,t,finalWord,htest.seq hloop,hinv,hword,hlen,hfalse,hcost⟩

end Maxwell.Cost.Structured.CountedShifted
