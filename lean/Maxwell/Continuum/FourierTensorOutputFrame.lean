import Maxwell.Continuum.FourierTensorGeneratedCoefficient
import Maxwell.Continuum.StructuredOutputFrame

/-! Wave generation and the complete alias traversal are silent, so
serialized earlier tensor coefficients remain intact. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536

theorem producer_silent : producerCode.silent=true := by
  have half_literal : Parts.literal (1/2:ℚ)=⟨1,0,2⟩ := by norm_num [Parts.literal]
  simp only [producerCode,cacheCode,cacheStepCode,encodedCode,cosineCode,finishControl,
    finishInstructions,halveControl,Control.prepend,List.foldr_cons,List.foldr_nil,Control.code,
    RationalDataflow.Instruction.code,half_literal]
  decide

theorem axisCode_silent (i : Fin 3) : (axisCode i).silent=true := by
  simp only [axisCode,factorCode,selectedProducerCode,Code.silent,Bool.and_eq_true]
  exact ⟨by fin_cases i <;> decide,⟨producer_silent,by decide⟩,by fin_cases i <;> decide⟩

theorem axesCode_silent : axesCode.silent=true := by
  simp only [axesCode,Code.silent,Bool.and_eq_true]
  exact ⟨axisCode_silent 0,axisCode_silent 1,axisCode_silent 2⟩

theorem generatedCoefficient_silent : generatedCoefficientCode.silent=true := by
  have ht : generatedTermCode.silent=true := by
    simp only [generatedTermCode,Code.silent,Bool.and_eq_true]
    exact ⟨axesCode_silent,by decide⟩
  have hs : aliasStepCode.silent=true := by
    simp only [aliasStepCode,Code.silent,Bool.and_eq_true]
    exact ⟨by decide,ht⟩
  simp only [generatedCoefficientCode,aliasLoopCode,countedProgram,Counted.code,
    Code.silent,Bool.and_eq_true]
  exact ⟨by decide,⟨by decide,hs,by decide⟩,by decide⟩

theorem generatedCoefficient_output {input : List Bool} {tape : ℕ→Bool} {cost : ℕ}
    {s t : Store} (e : Executes input tape generatedCoefficientCode cost s t) :
    t.val.output=s.val.output := e.silent generatedCoefficient_silent

#print axioms generatedCoefficient_output
end Maxwell.Continuum.Profile.WaveMachine.Runtime
