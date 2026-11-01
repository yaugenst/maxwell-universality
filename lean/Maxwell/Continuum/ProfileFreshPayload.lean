import Maxwell.Continuum.ProfileFreshStartup
import Maxwell.Cost.OutputCapture.InputPositions

/-! Actual profile production and retained serialization from runtime
precision4426, heap2600, and a finite fresh workspace. No coefficient table,
initialized rational bank, or execution trace is supplied by the caller. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
set_option maxHeartbeats 6500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] profileDegree profileWorkBits profileGrid runtimeBudget producerEmitCost

def freshPayloadCode : Code:=.seq freshStartupCode retainedPayloadCode
def freshPayloadCost (N heap : ℕ) : ℕ:=freshStartupCost N heap+6*producerEmitCost N 0+7

theorem retainedPayload_positions : retainedPayloadCode.protectsInputPositions=true:=by
  apply OutputCapture.code_positions
  decide

theorem freshPayload_executes (N heap : ℕ) (hh : heap.bits.length≤producerSize N)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (precision : Word s.val 4426 N) (heapWord : Word s.val 2600 heap)
    (fresh : ∀i∈freshTapes,s.val.tapes i=BitTape.blank) :
    ∃cost t,Executes input tape freshPayloadCode cost s t ∧cost ≤ freshPayloadCost N heap ∧
      BankArray.Word t.val 991 (profileBits N) ∧t.val.output=s.val.output ∧
      Word t.val 709 (bufferHeapEnd N (profileDegree N) heap) ∧
      t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor ∧
      t.val.tapes 988=s.val.tapes 988 ∧t.val.tapes 992=s.val.tapes 992 ∧
      (∀j,j<heap→t.val.memory j=s.val.memory j) := by
  obtain ⟨c0,a,e0,hc0,ready,frame⟩:=freshStartup_executes N heap input tape s precision heapWord fresh
  have positive : 1≤roundedWidth (profileGrid N) (producerSize N):=by unfold roundedWidth;omega
  have width := (Initialize.width dftRegisters).mono positive
  have savedWidth : (⟨0,0,0⟩:Parts).Width (roundedWidth (profileGrid N) (producerSize N)):=by
    simp only [Parts.Width]
    exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  obtain ⟨c1,t,values,e1,hc1,word,out,_,_,_,_,_,kept988,kept992,heapT,memory⟩:=
    retainedPayload_executes N heap hh Initialize.parts width ⟨0,0,0⟩ savedWidth input tape [] []
      (Nat.zero_le _) a ready.dimensions ready.allocation ready.blanks ready.rational ready.saved
      ready.inner ready.count ready.phase ready.glue ready.floor ready.array ready.seven ready.thirtySeven
      ready.inputClock ready.outputClock ready.swap ready.serializer ready.capture
  change c1 ≤ 6*producerEmitCost N 0+7 at hc1
  have positions:=e1.protectsInputPositions retainedPayload_positions
  refine ⟨c0+c1,t,e0.seq e1,by unfold freshPayloadCost;omega,word,out.trans frame.output,heapT,
    positions.1.trans frame.inputHead,positions.2.trans frame.randomCursor,
    kept988.trans (frame.tapes 988 (by decide +kernel)),
    kept992.trans (frame.tapes 992 (by decide +kernel)),?_⟩
  intro j hj
  rw [memory j hj,frame.memory]

#print axioms freshPayload_executes
end Maxwell.Continuum.Profile.Runtime
