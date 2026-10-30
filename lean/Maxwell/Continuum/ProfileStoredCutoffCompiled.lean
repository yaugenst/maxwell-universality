import Maxwell.Continuum.ProfileStoredCutoffCost

/-! Fixed Boolean execution from runtime precision and heap to the certified
cutoff query table. All scalar work, allocation, output writes and cleanup
are charged; the actual output tables lie below the returned heap cursor. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Calibration.RawCutoff
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget storedCutoffCost

theorem storedCutoff_compiled_run (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
    (v : ℕ→Parts) (hv : WidthBank dftRegisters (roundedWidth (profileGrid N) (producerSize N)) v)
    (saved : Parts) (hsv : saved.Width (roundedWidth (profileGrid N) (producerSize N)))
    (input : List Bool) (tape : ℕ→Bool) (inner oldWord : List Bool)
    (hlen : inner.length≤roundedWidth (profileGrid N) (producerSize N))
    (hold : oldWord.length≤runtimeBudget N) (s : Store)
    (hd : NatAssign.Bank dimensionIds (initialDimensions N) s.val)
    (hb : NatAssign.Bank allocationIds (bufferInput N 0 heap) s.val)
    (hz : ∀i∈startupBlanks,Blank s.val i) (hr : Ready dftRegisters v s)
    (hs : StoredParts.Stored 701 saved s.val) (hinner : BankArray.Word s.val 201 inner)
    (hcount : BankArray.Word s.val 700 oldWord)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (harray : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h205 : Blank s.val 205) (h215 : Blank s.val 215) (h216 : Blank s.val 216)
    (hcache : ∀i∈cacheFreshPorts,Blank s.val i) :
    ∃(t : Store) (result : CutoffTable N) (bank : ℕ→Parts) (word : List Bool),
      (runPriced (storedCutoffCode.compile.next input tape) (storedCutoffCost N oldWord.length+1) s.val).finished=
        some (t.place storedCutoffCode.size) ∧
      (runPriced (storedCutoffCode.compile.next input tape) (storedCutoffCost N oldWord.length+1) s.val).instructions≤
        2^84004*(N+1)^2088 ∧
      result.table.Ready t ∧ result.spare.OutputReady t ∧ Ready scaleSlots bank t ∧
      WidthBank scaleSlots (cutoffCacheWidth N) bank ∧ Good scaleSlots bank ∧
      BankArray.Word t.val 206 (profileDegree N).bits ∧ BankArray.Word t.val 201 word ∧
      word.length=(profileDegree N).bits.length ∧ Blank t.val 216 ∧
      Word t.val 709 result.heapEnd ∧ (∀i∈cacheDimensionIds,Blank t.val i) := by
  obtain ⟨cost,t,result,bank,word,ex,hcost,hr,hs,hb,hw,hg,hsaved,hcount,hlen',hz,hheap,hclean⟩ :=
    storedCutoff_executes N heap hh v hv saved hsv input tape inner oldWord hlen s
      hd hb hz hr hs hinner hcount hp hg hf harray h7 h37 h205 h215 h216 hcache
  obtain ⟨run,steps⟩ := ex.compiled_run (storedCutoffCost N oldWord.length+1) (by omega)
  exact ⟨t,result,bank,word,run,steps ▸ hcost.trans (storedCutoffCost_precision N oldWord.length hold),
    hr,hs,hb,hw,hg,hsaved,hcount,hlen',hz,hheap,hclean⟩

#print axioms storedCutoff_compiled_run
end Maxwell.Continuum.Profile.Runtime
