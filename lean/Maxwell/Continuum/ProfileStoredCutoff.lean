import Maxwell.Continuum.ProfileGeneratedCutoff
import Maxwell.Continuum.CutoffCacheFinishFrame

/-! The generated cutoff table is handed off with a proved free-memory cursor
and erased temporary descriptors. The program has no precision parameter. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Calibration.RawCutoff
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget

def storedCutoffCode : Code := .seq generatedCutoffCode cacheFinishCode
def storedCutoffCost (N len : ℕ) : ℕ := generatedCutoffCost N len+
  2^104*(monomialWorkingWidth (profileDegree N) (cacheSourceWidth N)+8)^2

theorem storedCutoff_executes (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
    (v : ℕ→Parts) (hv : WidthBank dftRegisters (roundedWidth (profileGrid N) (producerSize N)) v)
    (saved : Parts) (hsv : saved.Width (roundedWidth (profileGrid N) (producerSize N)))
    (input : List Bool) (tape : ℕ→Bool) (inner oldWord : List Bool)
    (hlen : inner.length≤roundedWidth (profileGrid N) (producerSize N)) (s : Store)
    (hd : NatAssign.Bank dimensionIds (initialDimensions N) s.val)
    (hb : NatAssign.Bank allocationIds (bufferInput N 0 heap) s.val)
    (hz : ∀i∈startupBlanks,Blank s.val i) (hr : Ready dftRegisters v s)
    (hs : StoredParts.Stored 701 saved s.val) (hinner : BankArray.Word s.val 201 inner)
    (hcount : BankArray.Word s.val 700 oldWord)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (harray : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h205 : Blank s.val 205) (h215 : Blank s.val 215) (h216 : Blank s.val 216)
    (hcache : ∀i∈cacheFreshPorts,Blank s.val i) :
    ∃(cost : ℕ) (t : Store) (result : CutoffTable N) (bank : ℕ→Parts) (word : List Bool),
      Executes input tape storedCutoffCode cost s t ∧ cost≤storedCutoffCost N oldWord.length ∧
      result.table.Ready t ∧ result.spare.OutputReady t ∧ RationalDataflow.Ready Calibration.RawCutoff.scaleSlots bank t ∧
      WidthBank Calibration.RawCutoff.scaleSlots (cutoffCacheWidth N) bank ∧
      Good Calibration.RawCutoff.scaleSlots bank ∧
      BankArray.Word t.val 206 (profileDegree N).bits ∧ BankArray.Word t.val 201 word ∧
      word.length=(profileDegree N).bits.length ∧ Blank t.val 216 ∧
      Word t.val 709 result.heapEnd ∧
      (∀i∈Calibration.RawCutoff.cacheDimensionIds,Blank t.val i) := by
  obtain ⟨c0,s0,result,bank,word,e0,hc0,a0,b0,r0,w0,g0,saved0,count0,len0,swap0,natural0,heap0,end0⟩ :=
    generatedCutoff_executes N heap hh v hv saved hsv input tape inner oldWord hlen s
      hd hb hz hr hs hinner hcount hp hg hf harray h7 h37 h205 h215 h216 hcache
  obtain ⟨c1,t,e1,hc1,heap1,clean1,z1,f1⟩ := cacheFinish_executes (profileDegree N) (cacheSourceWidth N)
    (cacheSourceHeap N heap) (cacheSourceHeap_bits N heap hh) input tape s0 natural0 heap0 r0.2
  have a1 := cacheFinish_table_frame a0 f1 z1
  have r1 := cacheFinish_rational_frame r0 f1 z1
  have b1 := cacheFinish_output_frame b0 f1 a1.scratch a1.seven
  refine ⟨c0+c1,t,result,bank,word,e0.seq e1,Nat.add_le_add hc0 hc1,a1,b1,r1,w0,g0,?_,?_,len0,?_,?_,clean1⟩
  · exact BankArray.word_of_eq (f1.tapes 206 (by decide)) saved0
  · exact BankArray.word_of_eq (f1.tapes 201 (by decide)) count0
  · exact blank_of_eq (f1.tapes 216 (by decide)) swap0
  · simpa only [end0] using heap1

#print axioms storedCutoff_executes
end Maxwell.Continuum.Profile.Runtime
