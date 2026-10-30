import Maxwell.Continuum.ChebyshevWaveProducer
import Maxwell.Continuum.StructuredTapeBound

/-! Tensor indices and completed factors can remain in logical registers
16 and above while the fixed wave producer runs. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536

theorem producer_tapesBelow : producerCode.tapesBelow 1048=true := by
  have half_literal : Parts.literal (1/2:ℚ)=⟨1,0,2⟩ := by norm_num [Parts.literal]
  simp only [producerCode,cacheCode,cacheStepCode,encodedCode,cosineCode,finishControl,
    finishInstructions,halveControl,Control.prepend,List.foldr_cons,List.foldr_nil,Control.code,
    RationalDataflow.Instruction.code,half_literal]
  decide

theorem producer_preserves_tape {input : List Bool} {tape : ℕ→Bool} {cost : ℕ}
    {s t : Store} (e : Executes input tape producerCode cost s t) (i : ℕ) (hi : 1048 ≤ i) :
    t.val.tapes i=s.val.tapes i := e.tapesBelow producer_tapesBelow i hi

theorem producer_preserves_parts {input : List Bool} {tape : ℕ→Bool} {cost : ℕ}
    {s t : Store} (e : Executes input tape producerCode cost s t) (j : ℕ) (hj : 16 ≤ j) :
    ∀i∈cellPorts j,t.val.tapes i=s.val.tapes i := by
  intro i hi
  apply producer_preserves_tape e
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl <;> simp only [positivePort,negativePort,denominatorPort] <;> omega

#print axioms producer_tapesBelow
#print axioms producer_preserves_parts
end Maxwell.Continuum.Profile.WaveMachine.Runtime
