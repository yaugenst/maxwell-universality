import Maxwell.Continuum.ProfileEmissionCost
import Maxwell.Continuum.ProfileProducerEmissionFrame

/-! One fixed Boolean program computes and serializes the literal radial
profile from runtime precision and heap words. No coefficient table or
execution trace is an input to this theorem. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget producerEmitCost

def generatedBitsCode : Code := .seq producerCode emitTableCode

theorem generatedBits_executes (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
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
    (hserial : ∀i∈serializerPorts,Blank s.val i) :
    ∃cost t values,Executes input tape generatedBitsCode cost s t ∧
      cost≤producerEmitCost N oldWord.length ∧
      t.val.output=(profileBits N).reverse++s.val.output ∧
      Ready StoredInteger.slots values t ∧
      WidthBank StoredInteger.slots (StoredDyadic.registerWidth (profileWorkBits N)
        (encodedTableWidth (profileDegree N) (runtimeBudget N))) values ∧
      Word t.val 144 (2^profileWorkBits N) ∧ DyadicFloor.Clean t.val ∧
      (∀i∈({201,726,727,728}:Finset ℕ),Blank t.val i) := by
  obtain ⟨c0,s0,result,e0,hc0,_,_⟩ := producer_allocated_executes N heap hh v hv saved hsv input tape
    inner oldWord hlen s hd hb hz hr hs hinner hcount hp hg hf harray h7 h37 h205 h215 h216
  have hm : (finalBuffer N heap s.val.memory).MetadataWidth
      (encodedTableWidth (profileDegree N) (runtimeBudget N)) := (allocated_metadata N heap hh s.val.memory).2
  have hWB := runtimeBudget_le_bufferWidth N (profileDegree N)
  change runtimeBudget N≤encodedTableWidth (profileDegree N) (runtimeBudget N) at hWB
  have hn := (runtimeBudget_parameters N).2.2.1.trans hWB
  have hP : (profileWorkBits N).bits.length≤encodedTableWidth (profileDegree N) (runtimeBudget N) := by
    have hbP := (producerSize_bounds N).2.2.2
    have hbW : producerSize N+1≤runtimeBudget N := by
      simpa only [runtimeBudget] using workingBudget_base (producerSize N)
    exact ((bits_le_of_le hbP).trans hbW).trans hWB
  have serial0 (i : ℕ) (hi : i∈serializerPorts) : Blank s0.val i :=
    blank_of_eq (e0.protectsSet serializerPorts producer_preserves_serializer i hi) (hserial i hi)
  obtain ⟨c1,t,values,e1,hc1,r1,w1,_,out1,p1,z1,blanks1⟩ := result.emit_executes hm hn hP input tape
    (serial0 726 (by decide)) (serial0 727 (by decide)) (serial0 728 (by decide))
  exact ⟨c0+c1,t,values,e0.seq e1,by unfold producerEmitCost;omega,
    by simpa only [e0.protectsOutput producer_preserves_output] using out1,r1,w1,p1,z1,blanks1⟩

theorem generatedBits_compiled_run (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
    (v : ℕ→Parts) (hv : WidthBank dftRegisters (roundedWidth (profileGrid N) (producerSize N)) v)
    (saved : Parts) (hsv : saved.Width (roundedWidth (profileGrid N) (producerSize N)))
    (input : List Bool) (tape : ℕ→Bool) (inner oldWord : List Bool)
    (hlen : inner.length≤roundedWidth (profileGrid N) (producerSize N)) (hold : oldWord.length≤runtimeBudget N)
    (s : Store) (hd : NatAssign.Bank dimensionIds (initialDimensions N) s.val)
    (hb : NatAssign.Bank allocationIds (bufferInput N 0 heap) s.val)
    (hz : ∀i∈startupBlanks,Blank s.val i) (hr : Ready dftRegisters v s)
    (hs : StoredParts.Stored 701 saved s.val) (hinner : BankArray.Word s.val 201 inner)
    (hcount : BankArray.Word s.val 700 oldWord)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (harray : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (h205 : Blank s.val 205) (h215 : Blank s.val 215) (h216 : Blank s.val 216)
    (hserial : ∀i∈serializerPorts,Blank s.val i) :
    ∃t values,
      (runPriced (generatedBitsCode.compile.next input tape)
        (producerEmitCost N oldWord.length+1) s.val).finished=some (t.place generatedBitsCode.size) ∧
      (runPriced (generatedBitsCode.compile.next input tape)
        (producerEmitCost N oldWord.length+1) s.val).instructions≤2^84003*(N+1)^2088 ∧
      t.val.output=(profileBits N).reverse++s.val.output ∧
      Ready StoredInteger.slots values t ∧
      WidthBank StoredInteger.slots (StoredDyadic.registerWidth (profileWorkBits N)
        (encodedTableWidth (profileDegree N) (runtimeBudget N))) values ∧
      Word t.val 144 (2^profileWorkBits N) ∧ DyadicFloor.Clean t.val ∧
      (∀i∈({201,726,727,728}:Finset ℕ),Blank t.val i) := by
  obtain ⟨cost,t,values,ex,hc,rest⟩ := generatedBits_executes N heap hh v hv saved hsv input tape
    inner oldWord hlen s hd hb hz hr hs hinner hcount hp hg hf harray h7 h37 h205 h215 h216 hserial
  obtain ⟨run,steps⟩ := ex.compiled_run (producerEmitCost N oldWord.length+1) (by omega)
  exact ⟨t,values,run,steps ▸ hc.trans (producerEmitCost_precision N oldWord.length hold),rest⟩

#print axioms generatedBits_compiled_run
end Maxwell.Continuum.Profile.Runtime
