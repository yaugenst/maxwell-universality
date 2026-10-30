import Maxwell.Continuum.RationalArctanProgram

/-! Framed composition of the arctangent primitive with additional stored words. -/

namespace Maxwell.Continuum.RationalArctan
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor

def extendedValues (v : ℕ→ℕ) (signs : ℕ→Sign) (N i : ℕ) : ℕ :=
  if i∈ids then values (v 610) (v 611) signs N i else v i

theorem program_extended (allIds : Finset ℕ) (hsub : ids⊆allIds)
    (hwork : ∀ i∈allIds, i∉ids → i∉workspace)
    (v : ℕ→ℕ) (signs : ℕ→Sign) (N W : ℕ) (hW : 1≤W)
    (hw : ∀ i∈ids, (v i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (program signs N) cost s t ∧
      cost≤costBound N W ∧
      NatAssign.Bank allIds (extendedValues v signs N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hc,ht,hf⟩ := program_executes v signs N W hW
    hw input tape s (fun i hi => hs i (hsub hi)) hsc
  refine ⟨cost,t,he,hc,?_,ht.scratch,hf⟩
  intro i hi
  by_cases ha : i∈ids
  · simpa only [extendedValues,ite_eq_left ha] using ht.bank i ha
  · simpa only [extendedValues,ite_eq_right ha] using
      word_of_eq (hf.tapes i (hwork i hi ha)) (hs i hi)

theorem extended_width (allIds : Finset ℕ) (hsub : ids⊆allIds)
    (v : ℕ→ℕ) (signs : ℕ→Sign) (N W : ℕ)
    (hw : ∀ i∈allIds, (v i).bits.length≤W) (i : ℕ) (hi : i∈allIds) :
    (extendedValues v signs N i).bits.length≤width N W := by
  have hw' : W≤width N W := by
    unfold width termWidth
    nlinarith only [Nat.zero_le (N*W),Nat.zero_le (N^2*W)]
  unfold extendedValues
  split_ifs with ha
  · exact values_width (v 610) (v 611) signs N N W le_rfl
      (hw 610 (hsub (by decide))) (hw 611 (hsub (by decide))) i
  · exact (hw i hi).trans hw'

#print axioms program_extended

end Maxwell.Continuum.RationalArctan
