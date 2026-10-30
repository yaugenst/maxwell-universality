import Maxwell.Continuum.CutoffCachePair
import Maxwell.Continuum.CutoffCacheDimensions

/-! The ten runtime cache descriptor words are tracked independently of
any concrete requested precision or generated profile values. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def cacheNaturalValues (D W heap : ℕ) (i : ℕ) : ℕ :=
  if i=720 then D else if i=721 then W else if i=722 then heap
  else if i=723 then monomialWorkingWidth D W else if i=724 then 4*(D+1)
  else if i=725 then 4*(D+1) else if i=726 then monomialWorkingWidth D W
  else if i=727 then cacheNextBase D W heap else if i=728 then 4*(D+1)*monomialWorkingWidth D W
  else if i=729 then cacheNextBase D W heap else 0


theorem cacheNatural_after_pair (D W H : ℕ) (s t : Store)
    (initial : NatAssign.Bank cacheDimensionIds (cacheDimensionValues D W H) s.val)
    (degree : RationalAccumulator.Word t.val 720 D)
    (size : RationalAccumulator.Word t.val 725 (4*(D+1)))
    (width : RationalAccumulator.Word t.val 726 (monomialWorkingWidth D W))
    (heap : RationalAccumulator.Word t.val 727 (cacheNextBase D W H))
    (temp : RationalAccumulator.Word t.val 728 (4*(D+1)*monomialWorkingWidth D W))
    (keep : ∀i∈([206,207,208,209,709,721,722,723,724,729]:List ℕ),t.val.tapes i=s.val.tapes i) :
    NatAssign.Bank cacheDimensionIds (cacheNaturalValues D W H) t.val := by
  intro i hi
  simp only [cacheDimensionIds,Finset.mem_Icc] at hi
  rcases hi with ⟨hlo,hhi⟩
  have from0 (j : ℕ) (hj : j∈([721,722,723,724,729]:List ℕ)) :
      RationalAccumulator.Word t.val j (cacheDimensionValues D W H j) := by
    exact RationalAccumulator.word_of_eq (keep j (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj ⊢;tauto))
      (initial j (by
        simp only [cacheDimensionIds,Finset.mem_Icc]
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        omega))
  interval_cases i <;> simp only [cacheNaturalValues,ite_true]
  · exact degree
  · simpa [cacheDimensionValues_eq,cacheWidthValues_eq,cacheDimensionInput] using from0 721 (by decide)
  · simpa [cacheDimensionValues_eq,cacheWidthValues_eq,cacheDimensionInput] using from0 722 (by decide)
  · simpa [cacheDimensionValues_eq,cacheWidthValues_eq] using from0 723 (by decide)
  · simpa [cacheDimensionValues_eq,cacheWidthValues_eq] using from0 724 (by decide)
  · exact size
  · exact width
  · exact heap
  · exact temp
  · simpa [cacheDimensionValues_eq] using from0 729 (by decide)

theorem cacheDimension_seed (D W H : ℕ) (s : Store)
    (h : NatAssign.Bank cacheDimensionIds (cacheDimensionValues D W H) s.val) :
    RationalAccumulator.Word s.val 720 D ∧
    RationalAccumulator.Word s.val 729 (cacheNextBase D W H) ∧
    NatAssign.Bank CacheAllocation.inputs (cacheAllocatorValues D W H 3) s.val := by
  refine ⟨?_,?_,?_⟩
  · simpa [cacheDimensionValues_eq,cacheWidthValues_eq,cacheDimensionInput] using h 720 (by decide)
  · simpa [cacheDimensionValues_eq] using h 729 (by decide)
  · intro i hi
    simp only [CacheAllocation.inputs,Finset.mem_Icc] at hi
    rcases hi with ⟨hlo,hhi⟩
    have hh := h i (by simp only [cacheDimensionIds,Finset.mem_Icc];omega)
    interval_cases i <;> simpa [cacheDimensionValues_eq,cacheAllocatorValues] using hh

#print axioms cacheNatural_after_pair
end Maxwell.Continuum.Profile.Runtime
