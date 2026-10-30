import Maxwell.Continuum.FourierTensorOutputFrame
import Maxwell.Continuum.RationalDataflowIntegerEmit

/-! The completed coefficient generator and serializer preserve all
external traversal counters and runtime array dimensions. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536

theorem generatedCoefficient_tapesBelow : generatedCoefficientCode.tapesBelow 1100=true := by
  have ht : generatedTermCode.tapesBelow 1100=true := by
    simp only [generatedTermCode,Code.tapesBelow,Bool.and_eq_true]
    exact ⟨Code.tapesBelow_mono axesCode_tapesBelow (by decide),by decide⟩
  have hs : aliasStepCode.tapesBelow 1100=true := by
    simp only [aliasStepCode,Code.tapesBelow,Bool.and_eq_true]
    exact ⟨by decide,ht⟩
  simp only [generatedCoefficientCode,aliasLoopCode,countedProgram,Counted.code,
    Code.tapesBelow,Bool.and_eq_true]
  exact ⟨by decide,⟨by decide,hs,by decide⟩,by decide⟩

theorem integerEmit_tapesBelow : (IntegerEmit.code 32).tapesBelow 1100=true := by decide

end Maxwell.Continuum.Profile.WaveMachine.Runtime
