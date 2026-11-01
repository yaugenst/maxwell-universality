import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.WordCall

/-! Charged cleanup of any finite counter word, including the fixed-width
noncanonical zero left by a countdown. Independent of either physical model. -/
namespace Maxwell.Cost.Structured.RuntimeCounter
open RationalAccumulator

theorem clear_executes (countTape : ℕ) (input : List Bool) (randomTape : ℕ→Bool)
    (bits : List Bool) (origin : ℤ) (s : Store)
    (hs : s.val.tapes countTape=BitTape.shifted bits origin) :
    ∃t,Executes input randomTape (.call (TapeOps.clear countTape)) (6*bits.length+4) s t ∧
      Blank t.val countTape ∧ BinaryPrecision.Frame {countTape} s.val t.val := by
  obtain ⟨t,he,ht,hf⟩ := WordCall.clear countTape input randomTape bits origin s hs
  refine ⟨t,he,⟨origin+bits.length,by simp only [ht,Function.update_self]⟩,
    hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  intro i hi
  rw [ht,Function.update_of_ne (show i≠countTape by simpa using hi)]

#print axioms clear_executes
end Maxwell.Cost.Structured.RuntimeCounter
