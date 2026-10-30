import Maxwell.Continuum.RationalTaylorRuntime

/-! Charged cleanup of the noncanonical fixed-width word left by a runtime
countdown. This restores an ordinary zero-valued word for repeated calls. -/
namespace Maxwell.Cost.Structured.RuntimeCounter
open RationalAccumulator

theorem clear_executes (countTape : ℕ) (input : List Bool) (randomTape : ℕ→Bool)
    (bits : List Bool) (origin : ℤ) (s : Store)
    (hs : s.val.tapes countTape=BitTape.shifted bits origin) :
    ∃t,Executes input randomTape (.call (TapeOps.clear countTape)) (6*bits.length+4) s t ∧
      Blank t.val countTape ∧ BinaryPrecision.Frame {countTape} s.val t.val := by
  obtain ⟨t,he,hp,ht,hf⟩ := TapeOps.clear_steps countTape input randomTape bits origin s.val s.property hs
  have e := Executes.call (TapeOps.clear countTape) s t (6*bits.length+3) he
    (by simp [TapeOps.clear,hp])
  refine ⟨Store.ofState t,by simpa only [Nat.add_assoc] using e,?_,?_⟩
  · exact ⟨origin+bits.length,ht⟩
  · refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
    intro i hi
    have hne : i≠countTape := by simpa using hi
    exact hf.2.2.2.2.2.1 i hne hne

#print axioms clear_executes
end Maxwell.Cost.Structured.RuntimeCounter
