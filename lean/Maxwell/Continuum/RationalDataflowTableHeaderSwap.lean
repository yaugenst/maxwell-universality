import Maxwell.Continuum.RationalDataflowWordSwapPlan
import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! Cached input/output buffers exchange roles by five actual metadata
word swaps. Their memory contents and the rational arithmetic bank persist. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def headerSlots : Finset ℕ := {200,202,203,204,205,210,212,213,214,215}
def headerSwapPlan : List (ℕ×ℕ) := [(200,210),(202,212),(203,213),(204,214),(205,215)]
def headerSwapCode : Code := WordSwapPlan.code 216 headerSwapPlan

def headerValues {n m : ℕ} (a : Table n) (b : Table m) (i : ℕ) : List Bool :=
  if i=200 then a.width else if i=202 then a.basePositive else if i=203 then a.baseNegative
  else if i=204 then a.baseDenominator else if i=205 then a.clock
  else if i=210 then b.width else if i=212 then b.basePositive else if i=213 then b.baseNegative
  else if i=214 then b.baseDenominator else if i=215 then b.clock else []

theorem headerSwap_values {n m : ℕ} (a : Table n) (b : Table m) (i : ℕ) (hi : i∈headerSlots) :
    WordSwapPlan.evaluate headerSwapPlan (headerValues a b) i=headerValues b a i := by
  simp only [headerSlots,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [WordSwapPlan.evaluate,WordSwapPlan.values,headerSwapPlan,headerValues]

theorem headerSlots_small (i : ℕ) (hi : i∈insert 216 headerSlots) : 200 ≤ i ∧ i≤216 := by
  simp only [headerSlots,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem Ready.headerSwap_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : RationalDataflow.Ready S v s)
    (f : BinaryPrecision.Frame (insert 216 headerSlots) s.val t.val) : RationalDataflow.Ready S v t := by
  constructor
  · intro i hi
    have hout : i∉insert 216 headerSlots := by
      intro him
      have hm := headerSlots_small i him
      exact outside_workspace S i (by omega) (Finset.mem_union_right _ hi)
    exact RationalAccumulator.word_of_eq (f.tapes i hout) (h.1 i hi)
  · intro i hi
    exact RationalAccumulator.blank_of_eq (f.tapes i (by
      intro him
      have := headerSlots_small i him
      omega)) (h.2 i hi)

theorem headerSwap_executes {n m : ℕ} (a : Table n) (b : Table m) (W : ℕ)
    (haMeta : a.MetadataWidth W) (hbMeta : b.MetadataWidth W)
    (S : Finset ℕ) (v : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) (hb : b.OutputReady s)
    (htemp : RationalAccumulator.Blank s.val 216) :
    ∃ cost t, Executes input tape headerSwapCode cost s t ∧ cost≤256*(W+1) ∧
      RationalDataflow.Ready S v t ∧ b.Ready t ∧ a.OutputReady t ∧
      RationalAccumulator.Blank t.val 216 ∧
      BinaryPrecision.Frame (insert 216 headerSlots) s.val t.val := by
  have bank : WordSwapPlan.Bank headerSlots (headerValues a b) s.val := by
    intro i hi
    simp only [headerSlots,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [headerValues,ite_true] using ha.width
    · simpa [headerValues] using ha.basePositive
    · simpa [headerValues] using ha.baseNegative
    · simpa [headerValues] using ha.baseDenominator
    · simpa [headerValues] using ha.clock
    · simpa [headerValues] using hb.width
    · simpa [headerValues] using hb.basePositive
    · simpa [headerValues] using hb.baseNegative
    · simpa [headerValues] using hb.baseDenominator
    · simpa [headerValues] using hb.clock
  have width : ∀i∈headerSlots,(headerValues a b i).length≤W := by
    intro i hi
    simp only [headerSlots,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [headerValues,ite_true] using haMeta.width
    · simpa [headerValues] using haMeta.basePositive
    · simpa [headerValues] using haMeta.baseNegative
    · simpa [headerValues] using haMeta.baseDenominator
    · simpa [headerValues] using haMeta.clock
    · simpa [headerValues] using hbMeta.width
    · simpa [headerValues] using hbMeta.basePositive
    · simpa [headerValues] using hbMeta.baseNegative
    · simpa [headerValues] using hbMeta.baseDenominator
    · simpa [headerValues] using hbMeta.clock
  obtain ⟨cost,t,hex,hcost,bt,_,temp,frame⟩ := WordSwapPlan.executes headerSlots 216 W (by decide)
    headerSwapPlan (by decide) (headerValues a b) width input tape s bank htemp
  have words (i : ℕ) (hi : i∈headerSlots) : BankArray.Word t.val i (headerValues b a i) := by
    simpa only [headerSwap_values a b i hi] using bt i hi
  have blank (i : ℕ) (hi : i<200) (h : RationalAccumulator.Blank s.val i) :
      RationalAccumulator.Blank t.val i := by
    apply RationalAccumulator.blank_of_eq (frame.tapes i _) h
    intro him
    have := headerSlots_small i him
    omega
  have scratch : BankArray.Scratch t.val :=
    ⟨blank 0 (by decide) ha.scratch.1,blank 1 (by decide) ha.scratch.2.1,
      blank 2 (by decide) ha.scratch.2.2.1,blank 3 (by decide) ha.scratch.2.2.2.1,
      blank 5 (by decide) ha.scratch.2.2.2.2.1,blank 6 (by decide) ha.scratch.2.2.2.2.2.1,
      blank 8 (by decide) ha.scratch.2.2.2.2.2.2.1,blank 9 (by decide) ha.scratch.2.2.2.2.2.2.2⟩
  have seven := blank 7 (by decide) ha.seven
  refine ⟨cost,t,hex,?_,Ready.headerSwap_frame hs frame,?_,?_,temp,frame⟩
  · simp only [headerSwapPlan,List.length_cons,List.length_nil] at hcost
    omega
  · refine ⟨scratch,seven,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [headerValues] using words 200 (by simp [headerSlots])
    · simpa [headerValues] using words 202 (by simp [headerSlots])
    · simpa [headerValues] using words 203 (by simp [headerSlots])
    · simpa [headerValues] using words 204 (by simp [headerSlots])
    · simpa [headerValues] using words 205 (by simp [headerSlots])
    · simpa only [frame.memory] using hb.positive
    · simpa only [frame.memory] using hb.negative
    · simpa only [frame.memory] using hb.denominator
  · refine ⟨scratch,seven,blank 37 (by decide) hb.packing,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [headerValues] using words 210 (by simp [headerSlots])
    · simpa [headerValues] using words 212 (by simp [headerSlots])
    · simpa [headerValues] using words 213 (by simp [headerSlots])
    · simpa [headerValues] using words 214 (by simp [headerSlots])
    · simpa [headerValues] using words 215 (by simp [headerSlots])
    · simpa only [frame.memory] using ha.positive
    · simpa only [frame.memory] using ha.negative
    · simpa only [frame.memory] using ha.denominator

#print axioms headerSwap_executes
end Maxwell.Continuum.RationalDataflow.PartArray
