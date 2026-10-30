import Maxwell.Continuum.ProfileAllocationFrame
import Maxwell.Continuum.ProfileProducerCost

/-! The fixed profile producer computes its dimensions, working widths,
buffer addresses, clocks and every encoded coefficient from runtime input.
No preallocated table contents or transform parameter words are assumed. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
attribute [local irreducible] profileDegree profileWorkBits profileGrid encodedCoefficient runtimeBudget

private theorem roundedRawWidth_le (grid U : ℕ) : roundedRawWidth U≤roundedWidth grid U := by
  unfold roundedWidth
  omega

def rawBuffer (N heap : ℕ) (memory : ℕ→Bool) : PartArray.Table (profileDegree N) :=
  memoryTable (profileDegree N) (runtimeBudget N) heap (runtimeBudget_parameters N).1 memory
def finalBuffer (N heap : ℕ) (memory : ℕ→Bool) : PartArray.Table (profileDegree N) :=
  memoryTable (profileDegree N) (bufferWidth N (profileDegree N)) (secondBufferBase N (profileDegree N) heap)
    ((runtimeBudget_parameters N).1.trans (runtimeBudget_le_bufferWidth N _)) memory
def producerCode : Code := .seq startupCode (.seq allocationCode encodedTableCode)
def producerCost (N oldLength : ℕ) : ℕ := startupCost N (runtimeBudget N) oldLength+
  (allocationCost N (profileDegree N) (producerSize N)+
    encodedTableCost (profileGrid N) (profileDegree N) (profileWorkBits N) (producerSize N)
      (runtimeBudget N) (profileDegree N).bits.length)

theorem encodedTableCode_preserves_allocator : ([660,709]:List ℕ).all
    (fun i => encodedTableCode.protectsTape i)=true := by decide

theorem producer_allocated_executes (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
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
    (h205 : Blank s.val 205) (h215 : Blank s.val 215) (h216 : Blank s.val 216) :
    ∃(cost : ℕ) (t : Store)
      (_result : EncodedTableResult N (runtimeBudget N) (finalBuffer N heap s.val.memory) t),
      Executes input tape producerCode cost s t ∧ cost≤producerCost N oldWord.length ∧
      Word t.val 660 N ∧ Word t.val 709 (bufferHeapEnd N (profileDegree N) heap) := by
  obtain ⟨hW,hbank,hn,hpow,hN⟩ := runtimeBudget_parameters N
  obtain ⟨hB,hN',hD'⟩ := producerSize_input_bounds N
  have hbig : 9≤runtimeBudget N := by
    have ha : producerSize N+1≤runtimeBudget N := by
      simpa only [runtimeBudget] using workingBudget_base (producerSize N)
    omega
  obtain ⟨c0,s0,e0,hc0,params,power,degree,grid,count,z0,f0,precision0⟩ :=
    startup_precise_executes N (runtimeBudget N) hN hbig input tape oldWord s hd hr.2 hz hcount
  let state0 := producerState_after_startup v hr hv saved hs hsv inner hinner hlen hp hg hf z0 f0 params power grid
  obtain ⟨c1,s1,e1,hc1,a1,b1,bank1,blank1,f1⟩ := allocation_executes N (profileDegree N) heap (producerSize N)
    hN' hD' hh hB input tape s0 (allocationBank_after_startup f0 hb precision0 degree)
    (startup_scratch harray z0 f0) (blank_of_eq (f0.tapes 7 (by decide)) h7)
    (blank_of_eq (f0.tapes 37 (by decide)) h37) (blank_of_eq (f0.tapes 205 (by decide)) h205)
    (blank_of_eq (f0.tapes 215 (by decide)) h215) (blank_of_eq (f0.tapes 216 (by decide)) h216)
  rw [f0.memory] at a1 b1
  change (rawBuffer N heap s.val.memory).OutputReady s1 at a1
  change (finalBuffer N heap s.val.memory).Ready s1 at b1
  have z1 : NatAssign.Scratch s1.val := by
    intro i hi
    interval_cases i
    · exact a1.scratch.1
    · exact a1.scratch.2.1
    · exact a1.scratch.2.2.1
    · exact a1.scratch.2.2.2.1
  let state1 := state0.allocation_frame z1 f1
  have size1 : Word s1.val 661 (profileDegree N) := by
    simpa [bufferAddressValues_eq,bufferWidthValues_eq,bufferBudgetValues_eq,bufferInput] using bank1 661 (by decide)
  have count1 := word_of_eq (f1.tapes 700 (by decide)) count
  obtain ⟨origin,count1⟩ := count1
  obtain ⟨ma,mb⟩ := allocated_metadata N heap hh s.val.memory
  have sepA := memoryTable_separated (profileDegree N) (runtimeBudget N) heap
    (runtimeBudget_parameters N).1 s.val.memory
  have sepB := memoryTable_separated (profileDegree N) (bufferWidth N (profileDegree N))
    (secondBufferBase N (profileDegree N) heap)
    ((runtimeBudget_parameters N).1.trans (runtimeBudget_le_bufferWidth N _)) s.val.memory
  have dis := tableSeparatedFrom_symm (memoryTable_separatedFrom
    (profileDegree N) (profileDegree N) (runtimeBudget N) (bufferWidth N (profileDegree N))
    heap (secondBufferBase N (profileDegree N) heap) (runtimeBudget_parameters N).1
    ((runtimeBudget_parameters N).1.trans (runtimeBudget_le_bufferWidth N _)) s.val.memory le_rfl)
  have fit : roundedRawWidth (producerSize N)≤addressValue (rawBuffer N heap s.val.memory).width := by
    change roundedRawWidth (producerSize N)≤addressValue (runtimeBudget N).bits
    rw [addressValue_bits]
    exact (roundedRawWidth_le (profileGrid N) (producerSize N)).trans hbank
  obtain ⟨_,hgrid,hdegree,hprecision⟩ := producerSize_bounds N
  obtain ⟨c2,t,result,e2,hc2⟩ := encoded_table_executes N (producerSize N) (runtimeBudget N) hW
    (rawBuffer N heap s.val.memory) (finalBuffer N heap s.val.memory) hgrid hdegree hprecision
    ma fit sepA dis mb (by simp only [finalBuffer,memoryTable,addressValue_bits];exact le_rfl)
    sepB hbank hn hpow input tape (profileDegree N).bits origin hn (addressValue_bits _) s1
    state1 a1 b1 size1 blank1 count1
  have precision1 : Word s1.val 660 N := by
    simpa [bufferAddressValues_eq,bufferWidthValues_eq,bufferBudgetValues_eq,bufferInput] using bank1 660 (by decide)
  have heap1 : Word s1.val 709 (bufferHeapEnd N (profileDegree N) heap) := by
    simpa [bufferAddressValues_eq] using bank1 709 (by decide)
  exact ⟨c0+(c1+c2),t,result,e0.seq (e1.seq e2),by unfold producerCost;omega,
    word_of_eq (e2.protectsTape 660 (List.all_eq_true.mp encodedTableCode_preserves_allocator 660 (by decide))) precision1,
    word_of_eq (e2.protectsTape 709 (List.all_eq_true.mp encodedTableCode_preserves_allocator 709 (by decide))) heap1⟩

#print axioms producer_allocated_executes
end Maxwell.Continuum.Profile.Runtime
