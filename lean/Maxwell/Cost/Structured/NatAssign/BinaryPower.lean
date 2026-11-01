import Maxwell.Cost.RoutingPorts.Primitives
import Maxwell.Cost.Structured.NatAssign

/-! Actual binary exponentiation in a natural-word bank. Only the result
word and the cleared counter are written; surrounding data is preserved. -/
namespace Maxwell.Cost.Structured.NatAssign
open RationalAccumulator (Word Blank)

theorem binaryPower (ids : Finset ℕ) (source counter target : ℕ)
    (hs : source∈ids) (hc : counter∈ids) (ht : target∈ids)
    (hsc : source≠counter) (hst : source≠target) (hct : counter≠target)
    (v : ℕ→ℕ) (hcv : v counter=0) (htv : v target=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hb : Bank ids v s.val) :
    ∃cost t,Executes input tape (RoutingPorts.powerCode source counter target) cost s t ∧
      cost≤(v source+1)*(13*(v source).bits.length+25)+21*(v source).bits.length+27 ∧
      Bank ids (Function.update v target (2^(v source))) t.val ∧
      BinaryPrecision.Frame {counter,target} s.val t.val := by
  have bc : Blank s.val counter :=
    (RationalAccumulator.zero_word_iff_blank _ _).mp (by simpa only [hcv] using hb counter hc)
  have bt : Blank s.val target :=
    (RationalAccumulator.zero_word_iff_blank _ _).mp (by simpa only [htv] using hb target ht)
  obtain ⟨cost,t,he,hcost,hw,hblank,hf⟩ := RoutingPorts.power source counter target
    hsc hst hct input tape (v source) s (hb source hs) bc bt
  refine ⟨cost,t,he,hcost,?_,hf⟩
  intro i hi
  by_cases hit : i=target
  · subst i;simpa only [Function.update_self] using hw
  · by_cases hic : i=counter
    · subst i
      simpa only [Function.update_of_ne hct,hcv] using
        (RationalAccumulator.zero_word_iff_blank _ _).mpr hblank
    · apply RationalAccumulator.word_of_eq (hf.tapes i (by simp [hit,hic]))
      simpa only [Function.update_of_ne hit] using hb i hi

#print axioms binaryPower
end Maxwell.Cost.Structured.NatAssign
