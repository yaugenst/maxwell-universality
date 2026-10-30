import Maxwell.Continuum.ProfileParameterSetup
import Maxwell.Continuum.RationalDataflowWordReplace

/-! Precision is the only numeric producer parameter supplied here.
The actual degree, work precision, grid, scale and outer countdown are all
computed by fixed runtime programs. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
attribute [local irreducible] profileDegree profileWorkBits profileGrid

def startupBlanks : Finset ℕ := {144,145,146,640,652,653,667,668,669}
def startupWorkspace : Finset ℕ := insert 700 (dimensionWorkspace∪parameterWorkspace)
def startupCode : Code := .seq dimensionCode (.seq parameterCode (WordReplace.code 661 700))
def startupCost (N W oldLength : ℕ) : ℕ :=
  2^120*(W+2)^2+parameterCost (profileWorkBits N) (dimensionWidth W)+
    6*oldLength+15*(profileDegree N).bits.length+21

theorem startup_executes (N W : ℕ) (hN : N.bits.length≤W) (hW : 9≤W)
    (input : List Bool) (tape : ℕ→Bool) (oldWord : List Bool) (s : Store)
    (hs : NatAssign.Bank dimensionIds (initialDimensions N) s.val) (hz : NatAssign.Scratch s.val)
    (hblank : ∀i∈startupBlanks,Blank s.val i) (hcount : BankArray.Word s.val 700 oldWord) :
    ∃cost t,Executes input tape startupCode cost s t ∧ cost≤startupCost N W oldWord.length ∧
      DFTParameters (profileDegree N) (profileWorkBits N) t ∧
      Word t.val 144 (2^profileWorkBits N) ∧ Word t.val 661 (profileDegree N) ∧
      Word t.val 664 (profileGrid N) ∧ Word t.val 700 (profileDegree N) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame startupWorkspace s.val t.val := by
  obtain ⟨c0,s0,e0,hc0,b0,z0,f0,_,degree0,work0,grid0⟩ := dimensions_executes N W hN hW input tape s hs hz
  have extra (i : ℕ) (hi : i∈startupBlanks) : Blank s0.val i := by
    apply blank_of_eq (f0.tapes i _) (hblank i hi)
    have hd : Disjoint startupBlanks dimensionWorkspace := by decide
    exact fun hh => Finset.disjoint_left.mp hd hi hh
  have bank : NatAssign.Bank parameterIds
      (parameterInput (profileDegree N) (profileWorkBits N) (profileGrid N)) s0.val := by
    intro i hi
    simp only [parameterIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | simpa only [parameterInput,ite_true] using degree0
      | simpa [parameterInput] using work0
      | simpa [parameterInput] using grid0
      | simpa [parameterInput] using (zero_word_iff_blank _ _).mpr (extra _ (by decide))
  have degreeWidth : (profileDegree N).bits.length≤dimensionWidth W := by
    simpa [finalDimensions_eq,scannedValues,degreeValues_eq] using finalDimensions_width N W hN hW 661 (by decide)
  have workWidth : (profileWorkBits N).bits.length≤dimensionWidth W := by
    simpa only [finalDimensions_work] using finalDimensions_width N W hN hW 663 (by decide)
  have gridWidth : (profileGrid N).bits.length≤dimensionWidth W := by
    simpa only [finalDimensions_grid] using finalDimensions_width N W hN hW 664 (by decide)
  obtain ⟨c1,s1,e1,hc1,parameters1,power1,degree1,grid1,z1,f1⟩ := parameters_executes
    (profileDegree N) (profileWorkBits N) (profileGrid N) (dimensionWidth W)
    (by unfold dimensionWidth;omega) degreeWidth workWidth gridWidth input tape s0 bank z0
    (extra 144 (by decide)) (extra 146 (by decide))
  have f01 : BinaryPrecision.Frame (dimensionWorkspace∪parameterWorkspace) s.val s1.val :=
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  have count1 := BankArray.word_of_eq (f01.tapes 700 (by decide)) hcount
  obtain ⟨t,e2,count2,f2⟩ := WordReplace.executes 661 700 (by decide) input tape
    (profileDegree N).bits oldWord s1 degree1 count1
  have keep (i : ℕ) (hi : i≠700) := f2.2.2.2.2.2.1 i hi
  have f2' : BinaryPrecision.Frame {700} s1.val t.val :=
    ⟨f2.1,f2.2.1,f2.2.2.1,f2.2.2.2.1,f2.2.2.2.2.1,by
      intro i hi;exact keep i (by simpa using hi)⟩
  refine ⟨c0+(c1+_),t,e0.seq (e1.seq e2),?_,?_,
    word_of_eq (keep 144 (by decide)) power1,word_of_eq (keep 661 (by decide)) degree1,
    word_of_eq (keep 664 (by decide)) grid1,count2,?_,
    (f01.mono (by simp [startupWorkspace])).trans (f2'.mono (by simp [startupWorkspace]))⟩
  · unfold startupCost
    omega
  · exact ⟨word_of_eq (keep 663 (by decide)) parameters1.precision,
      word_of_eq (keep 667 (by decide)) parameters1.one,
      word_of_eq (keep 668 (by decide)) parameters1.guard,
      word_of_eq (keep 669 (by decide)) parameters1.range,
      word_of_eq (keep 652 (by decide)) parameters1.phaseRange,
      word_of_eq (keep 653 (by decide)) parameters1.phasePrecision,
      word_of_eq (keep 640 (by decide)) parameters1.gluePrecision⟩
  · intro i hi
    exact blank_of_eq (keep i (by omega)) (z1 i hi)

#print axioms startup_executes
end Maxwell.Continuum.Profile.Runtime
