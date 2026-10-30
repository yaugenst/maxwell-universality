import Maxwell.Continuum.ProfileCutoffCache
import Maxwell.Continuum.ProfileCacheFootprint

/-! One fixed Boolean program constructs the profile and its cutoff cache
from runtime precision and heap words. Every coefficient and cache cell is
actually computed; no precomputed table is an input to this theorem. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget

def generatedCutoffCode : Code := .seq producerCode cutoffCacheCode
def generatedCutoffCost (N len : ℕ) : ℕ := producerCost N len+cutoffCacheCost N

theorem generatedCutoff_executes (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
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
      Executes input tape generatedCutoffCode cost s t ∧ cost≤generatedCutoffCost N oldWord.length ∧
      result.table.Ready t ∧ result.spare.OutputReady t ∧ RationalDataflow.Ready Calibration.RawCutoff.scaleSlots bank t ∧
      WidthBank Calibration.RawCutoff.scaleSlots (cutoffCacheWidth N) bank ∧
      Good Calibration.RawCutoff.scaleSlots bank ∧
      BankArray.Word t.val 206 (profileDegree N).bits ∧ BankArray.Word t.val 201 word ∧
      word.length=(profileDegree N).bits.length ∧ Blank t.val 216 ∧
      NatAssign.Bank Calibration.RawCutoff.cacheDimensionIds
        (cacheNaturalValues (profileDegree N) (cacheSourceWidth N) (cacheSourceHeap N heap)) t.val ∧
      Word t.val 709 (cacheSourceHeap N heap) ∧
      result.heapEnd=Calibration.RawCutoff.cacheEndBase (profileDegree N) (cacheSourceWidth N) (cacheSourceHeap N heap) := by
  obtain ⟨c0,s0,r,e0,hc0,N0,heap0⟩ := producer_allocated_executes N heap hh v hv saved hsv
    input tape inner oldWord hlen s hd hb hz hr hs hinner hcount hp hg hf harray h7 h37 h205 h215 h216
  have clean0 (i : ℕ) (hi : i∈cacheFreshPorts) : Blank s0.val i :=
    blank_of_eq (e0.protectsSet cacheFreshPorts producer_protects_cache i hi) (hcache i hi)
  obtain ⟨c1,t,result,bank,word,e1,hc1,ready,spare,br,bw,bg,sv,cnt,len,blank,natural,heap1,end1⟩ :=
    cutoffCache_executes s0 r hh N0 heap0
      (fun i hi=>clean0 i (Finset.mem_union_right _ hi)) r.indexBlanks
      (fun i hi=>clean0 i (Finset.mem_union_left _ hi)) input tape
  exact ⟨c0+c1,t,result,bank,word,e0.seq e1,Nat.add_le_add hc0 hc1,
    ready,spare,br,bw,bg,sv,cnt,len,blank,natural,heap1,end1⟩

#print axioms generatedCutoff_executes
end Maxwell.Continuum.Profile.Runtime
