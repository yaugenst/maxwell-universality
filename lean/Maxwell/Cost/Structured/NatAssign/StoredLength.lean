import Maxwell.Cost.WordLength
import Maxwell.Cost.Structured.NatAssign

/-! A fixed tape scan writes the binary length of a stored natural. -/
namespace Maxwell.Cost.Structured.NatAssign
open RationalAccumulator
set_option maxHeartbeats 1500000

theorem stored_length (ids : Finset ℕ) (source target : ℕ) (hne : source≠target)
    (hsid : source∈ids) (htid : target∈ids) (ht4 : 4≤target)
    (v : ℕ→ℕ) (hv : v target=0) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Bank ids v s.val) (hz : Scratch s.val) :
    ∃cost t,Executes input tape (WordLength.code source target) cost s t ∧
      cost≤48*((v source).bits.length+1)^2+1 ∧
      Bank ids (Function.update v target (v source).bits.length) t.val ∧ Scratch t.val ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨so,hw⟩ := hs source hsid
  have hz' : Blank s.val target := by simpa only [hv,zero_word_iff_blank] using hs target htid
  obtain ⟨targetOrigin,hblank⟩ := hz'
  obtain ⟨c,t,e,hc,hsource,htarget,ft⟩ := WordLength.executes source target hne input tape
    (v source).bits so targetOrigin s hw hblank
  have frame : BinaryPrecision.Frame {target} s.val t.val := by
    refine ⟨ft.1,ft.2.1,ft.2.2.1,ft.2.2.2.1,ft.2.2.2.2.1,?_⟩
    intro i hi
    by_cases he : i=source
    · subst i
      exact hsource.trans hw.symm
    · exact ft.2.2.2.2.2.1 i he (by simpa using hi)
  refine ⟨c,t,e,hc,?_,?_,frame⟩
  · intro i hi
    by_cases he : i=target
    · subst i
      exact ⟨targetOrigin,by simpa only [Function.update_self] using htarget⟩
    · simpa only [Function.update_of_ne he] using word_of_eq
        (frame.tapes i (by simpa using he)) (hs i hi)
  · intro i hi
    exact blank_of_eq (frame.tapes i (by simp only [Finset.mem_singleton];omega)) (hz i hi)

#print axioms stored_length
end Maxwell.Cost.Structured.NatAssign
