import Maxwell.Continuum.ProfileAllocatedCost

/-! Actual Boolean execution of the fixed profile producer, including all
allocation, scalar approximation, table writes and endpoint correction. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget producerCost

theorem producer_compiled_run (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
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
    (h205 : Blank s.val 205) (h215 : Blank s.val 215) (h216 : Blank s.val 216) :
    ∃t : Store,
      (runPriced (producerCode.compile.next input tape) (producerCost N oldWord.length+1) s.val).finished=
        some (t.place producerCode.size) ∧
      (runPriced (producerCode.compile.next input tape) (producerCost N oldWord.length+1) s.val).instructions≤
        2^84002*(N+1)^2088 ∧
      Nonempty (EncodedTableResult N (runtimeBudget N) (finalBuffer N heap s.val.memory) t) := by
  obtain ⟨cost,t,result,e,hcost,_,_⟩ := producer_allocated_executes N heap hh v hv saved hsv input tape
    inner oldWord hlen s hd hb hz hr hs hinner hcount hp hg hf harray h7 h37 h205 h215 h216
  obtain ⟨hrun,hsteps⟩ := e.compiled_run (producerCost N oldWord.length+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hcost.trans (producerCost_precision N oldWord.length hold),⟨result⟩⟩

#print axioms producer_compiled_run
end Maxwell.Continuum.Profile.Runtime
