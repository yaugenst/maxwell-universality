import Maxwell.Continuum.RationalDataflowRetainedCells
import Maxwell.Cost.Structured.WordLiteral
import Maxwell.Cost.Structured.WordCleanup

/-! The actual root numerator and denominator become a raw reciprocal.
The comparison bank is then cleared before rational array arithmetic resumes. -/
namespace Maxwell.Continuum.Calibration.RationalRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def comparisonWords : List ℕ := [30,31,32,33,34,35,36]
def inverseParts (num den : ℕ) : Parts := ⟨den,0,num⟩
def inverseStoreCode (target : ℕ) : Code :=
  .seq (WordReplace.code 548 (positivePort target))
    (.seq (WordLiteral.code (negativePort target) 0)
      (.seq (WordReplace.code 32 (denominatorPort target)) (WordCleanup.code comparisonWords)))
def inverseStoreChanged (target : ℕ) : Finset ℕ := cellPorts target∪RationalMagnitude.ids

theorem inverseParts_value (num den : ℕ) : (inverseParts num den).value=((num:ℚ)/den)⁻¹ := by
  simp [inverseParts,Parts.value,inv_div]

theorem inverseStore_executes (S : Finset ℕ) (target : ℕ) (ht : target∈S)
    (v : ℕ→Parts) (num den W : ℕ) (oldWidth : (v target).Width W)
    (numWidth : num.bits.length≤W) (denWidth : den.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells S v s.val) (numerator : Word s.val 32 num) (denominator : Word s.val 548 den)
    (oldComparison : WordCleanup.Bounded comparisonWords W s.val)
    (temporary : ∀i∈temporaryPorts,Blank s.val i) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (inverseStoreCode target) cost s t ∧ cost≤100*(W+1) ∧
      Ready S (Function.update v target (inverseParts num den)) t ∧
      BinaryPrecision.Frame (inverseStoreChanged target) s.val t.val := by
  have hp:=positivePort_ge target
  have hm:=negativePort_ge target
  have hd:=denominatorPort_ge target
  have pm : positivePort target≠negativePort target := by unfold positivePort negativePort; omega
  have pd : positivePort target≠denominatorPort target := by unfold positivePort denominatorPort; omega
  have md : negativePort target≠denominatorPort target := by unfold negativePort denominatorPort; omega
  obtain ⟨u,e0,p0,f0⟩ := WordReplace.executes 548 (positivePort target) (by omega)
    input tape den.bits (v target).positive.bits s denominator (cells target ht).1
  have f0' := StoredParts.copy_frame f0
  have oldNegative : Word u.val (negativePort target) (v target).negative :=
    RationalAccumulator.word_of_eq (f0.2.2.2.2.2.1 _ pm.symm) (cells target ht).2.1
  obtain ⟨w,e1,m1,f1⟩ := WordLiteral.executes (negativePort target) 0 input tape
    (v target).negative.bits u oldNegative
  have oldDenominator : Word w.val (denominatorPort target) (v target).denominator :=
    RationalAccumulator.word_of_eq (f1.tapes _ (by simpa only [Finset.mem_singleton] using md.symm))
      (RationalAccumulator.word_of_eq (f0.2.2.2.2.2.1 _ pd.symm) (cells target ht).2.2)
  have numWord : Word w.val 32 num := RationalAccumulator.word_of_eq (f1.tapes _ (by simp;omega))
    (RationalAccumulator.word_of_eq (f0.2.2.2.2.2.1 _ (by omega)) numerator)
  obtain ⟨z,e2,d2,f2⟩ := WordReplace.executes 32 (denominatorPort target) (by omega)
    input tape num.bits (v target).denominator.bits w numWord oldDenominator
  have f2' := StoredParts.copy_frame f2
  have writeFrame : BinaryPrecision.Frame (cellPorts target) s.val z.val :=
    (f0'.mono (by simp [cellPorts])).trans
      ((f1.mono (by simp [cellPorts])).trans (f2'.mono (by simp [cellPorts])))
  have stored : StoredParts.Stored (positivePort target) (inverseParts num den) z.val := by
    refine ⟨?_,?_,d2⟩
    · exact RationalAccumulator.word_of_eq (f2.2.2.2.2.2.1 _ pd)
        (RationalAccumulator.word_of_eq (f1.tapes _ (by simpa only [Finset.mem_singleton] using pm)) p0)
    · exact RationalAccumulator.word_of_eq (f2.2.2.2.2.2.1 _ md) m1
  have written := cells.write stored writeFrame
  have comparison : WordCleanup.Bounded comparisonWords W z.val := by
    intro i hi
    obtain ⟨xs,hx,word⟩:=oldComparison i hi
    have low : i<1000 := by simp only [comparisonWords,List.mem_cons,List.not_mem_nil,or_false] at hi;omega
    exact ⟨xs,hx,BankArray.word_of_eq (writeFrame.tapes i (by simp [cellPorts];omega)) word⟩
  obtain ⟨c3,t,e3,h3,blank,f3⟩ := WordCleanup.executes comparisonWords W input tape z comparison
  have f3' : BinaryPrecision.Frame RationalMagnitude.ids z.val t.val := by
    exact (by decide : comparisonWords.toFinset=RationalMagnitude.ids) ▸ f3
  have allFrame := writeFrame.mono (Finset.subset_union_left (s₂:=RationalMagnitude.ids))
  have frame : BinaryPrecision.Frame (inverseStoreChanged target) s.val t.val :=
    allFrame.trans (f3'.mono Finset.subset_union_right)
  have finalCells : Cells S (Function.update v target (inverseParts num den)) t.val := by
    apply written.transfer
    intro i hi
    apply f3'.tapes
    simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton]
    omega
  have work : ∀i∈workPorts,Blank t.val i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · have out : i∉inverseStoreChanged target := by
        simp only [temporaryPorts,Finset.mem_insert,Finset.mem_singleton] at hi
        simp only [inverseStoreChanged,cellPorts,RationalMagnitude.ids,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton]
        omega
      exact RationalAccumulator.blank_of_eq (frame.tapes i out) (temporary i hi)
    · apply blank i
      simpa only [comparisonWords,RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton,
        List.mem_cons,List.not_mem_nil,or_false] using hi
  have finalScratch : NatAssign.Scratch t.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (frame.tapes i _) (scratch i hi)
    simp only [inverseStoreChanged,cellPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton]
    omega
  refine ⟨_,t,e0.seq (e1.seq (e2.seq e3)),?_,finalCells.ready work finalScratch,frame⟩
  have length : comparisonWords.length=7 := rfl
  rw [length] at h3
  have zero : (0:ℕ).bits.length=0 := rfl
  rw [zero]
  rcases oldWidth with ⟨wp,wm,wd⟩
  omega

#print axioms inverseStore_executes
end Maxwell.Continuum.Calibration.RationalRoot
