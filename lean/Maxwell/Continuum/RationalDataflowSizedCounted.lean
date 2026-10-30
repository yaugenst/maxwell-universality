import Maxwell.Continuum.RationalDataflowCounted

/-! Runtime loops whose body cost includes the actual fixed-width index word. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem counted_executes_sized (countTape : ℕ) (origin : ℤ) (body : Code)
    (input : List Bool) (randomTape : ℕ→Bool) (wordLength : ℕ)
    (invariant : ℕ→Store→Prop) (bound : ℕ→ℕ)
    (stable : ∀ n s t, CountedShifted.Frame countTape s t → invariant n s → invariant n t)
    (bodyCorrect : ∀ n xs s, invariant (n+1) s →
      s.val.tapes countTape=BitTape.shifted xs origin → addressValue xs=n → xs.length=wordLength →
      ∃ cost t, Executes input randomTape body cost s t ∧ invariant n t ∧
        t.val.tapes countTape=BitTape.shifted xs origin ∧ cost≤bound n)
    (n : ℕ) (xs : List Bool) (s : Store) (hvalue : addressValue xs=n)
    (hword : s.val.tapes countTape=BitTape.shifted xs origin) (hlen : xs.length=wordLength)
    (hinvariant : invariant n s) :
    ∃ cost t finalWord, Executes input randomTape (countedProgram countTape body) cost s t ∧
      invariant 0 t ∧ t.val.tapes countTape=BitTape.shifted finalWord origin ∧
      finalWord.length=wordLength ∧ t.val.registers 29=false ∧
      cost≤(n+1)*(13*wordLength+15)+∑ k∈Finset.range n,bound k := by
  induction n generalizing xs s with
  | zero =>
    obtain ⟨t,ht,hw,hz,hf⟩ := CountedShifted.test_executes countTape origin input randomTape s xs hword
    have hfalse := hz.mpr hvalue
    refine ⟨13*xs.length+14+1,t,subtractBit true xs,
      ht.seq (Executes.done hfalse),stable 0 s t hf hinvariant,hw,
      (subtractBit_length true xs).trans hlen,hfalse,?_⟩
    simp [hlen]
  | succ n ih =>
    obtain ⟨tested,htest,hw,hz,hf⟩ := CountedShifted.test_executes countTape origin input randomTape s xs hword
    have hpositive : 0<addressValue xs := by omega
    have hdecrease : addressValue (subtractBit true xs)=n := by
      rw [subtractBit_pred xs hpositive,hvalue]
      omega
    have htrue : tested.val.registers 29=true := by
      cases hb : tested.val.registers 29 with
      | true => rfl
      | false => have := hz.mp hb; omega
    have hnewlen := (subtractBit_length true xs).trans hlen
    obtain ⟨bodyCost,middle,hbody,hmInv,hmWord,hmCost⟩ := bodyCorrect n (subtractBit true xs) tested
      (stable (n+1) s tested hf hinvariant) hw hdecrease hnewlen
    obtain ⟨restCost,t,finalWord,hrest,htInv,htWord,htLength,htFalse,htCost⟩ :=
      ih (subtractBit true xs) middle hdecrease hmWord hnewlen hmInv
    change Executes input randomTape
      (.seq (CountedShifted.test countTape) (.loop 29 (.seq body (CountedShifted.test countTape))))
      restCost middle t at hrest
    cases hrest with
    | seq restTest restLoop =>
      refine ⟨_,t,finalWord,htest.seq (Executes.more htrue (hbody.seq restTest) restLoop),
        htInv,htWord,htLength,htFalse,?_⟩
      rw [Finset.sum_range_succ]
      rw [hlen]
      nlinarith only [htCost,hmCost]

#print axioms counted_executes_sized

end Maxwell.Continuum.RationalDataflow
