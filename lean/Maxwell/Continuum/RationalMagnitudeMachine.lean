import Maxwell.Cost.IntegerNormSquare.Magnitude
import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Framed canonical magnitude extraction from a pair of stored natural numerator channels. -/

namespace Maxwell.Continuum.RationalMagnitude
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator

def ids : Finset ℕ := {30,31,32,33,34,35,36}
def workspace : Finset ℕ := {0,1,2,3}∪ids
def program : Code := IntegerNormSquare.magnitudeCode

theorem executes (allIds : Finset ℕ) (hsub : ids⊆allIds)
    (hids : ∀ i∈allIds, 4 ≤ i) (v : ℕ→ℕ) (hzero : v 34=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape program cost s t ∧
      cost≤300*((v 30).bits.length+(v 31).bits.length+4) ∧
      NatAssign.Bank allIds (Function.update v 34 (IntegerNormSquare.magnitude (v 30) (v 31))) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val ∧
      t.val.registers 23=SignedDifference.sign (v 30).bits (v 31).bits := by
  have bank : Bank s.val v := by
    intro i hi hj
    exact hs i (hsub (by simp only [ids,Finset.mem_insert,Finset.mem_singleton]; omega))
  have ready : Scratch s.val 0 :=
    ⟨hsc 0 (by decide),(zero_word_iff_blank _ _).mpr (hsc 1 (by decide)),
      hsc 2 (by decide),hsc 3 (by decide)⟩
  obtain ⟨cost,t,hc,he,hb,hr,hf,hsg⟩ := IntegerNormSquare.store_magnitude_signed input tape v s bank ready hzero
  have frame : BinaryPrecision.Frame workspace s.val t.val := by
    refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
    intro i hi
    simp only [workspace,ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    exact hf.2.2.2.2.2.1 i (by omega) (by omega)
  refine ⟨cost,t,he,hc,?_,?_,frame,hsg⟩
  · intro i hi
    by_cases hm : i∈ids
    · simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hm
      exact hb i (by omega) (by omega)
    · have hn : i≠34 := by intro he; subst i; exact hm (by decide)
      have ho : i∉workspace := by
        have h4 := hids i hi
        simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        exact not_or_intro (by omega) hm
      simpa only [Function.update_of_ne hn] using word_of_eq (frame.tapes i ho) (hs i hi)
  · intro i hi
    interval_cases i
    · exact hr.1
    · exact (zero_word_iff_blank _ _).mp hr.2.1
    · exact hr.2.2.1
    · exact hr.2.2.2

#print axioms executes

end Maxwell.Continuum.RationalMagnitude
