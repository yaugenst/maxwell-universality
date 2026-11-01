import Maxwell.Continuum.CalibrationInverseAllocated
import Maxwell.Continuum.CalibrationGeneratedInverseTapeBound
import Maxwell.Cost.Structured.NatAssign.LengthSumTapeBound

/-! Descriptor preparation and cached inversion preserve the unused tail
of the source arithmetic bank. -/
namespace Maxwell.Continuum.Calibration.AllocatedInverse
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem tapeBound : code.tapeBound ≤ 1123 := by
  change max InverseDescriptor.startCode.tapeBound
    ArrayDecodeMachine.generatedInverseCode.tapeBound ≤ 1123
  refine max_le ?_ ArrayDecodeMachine.generatedInverse_tapeBound
  simp only [InverseDescriptor.startCode,InverseDescriptor.code,Code.tapeBound,max_le_iff]
  refine ⟨by decide,by decide,?_,?_⟩
  · apply NatAssign.LengthSum.initializedCode_tapeBound 530 531 1024 1123 InverseDescriptor.sources
      (by decide) (by decide) (by decide) (by decide)
    intro i hi
    have bound : i∈InverseDescriptor.sourceIds := by
      simpa only [InverseDescriptor.sources,Finset.mem_sort] using hi
    simp only [InverseDescriptor.sourceIds,Finset.mem_union,Finset.mem_Icc,
      Finset.mem_insert,Finset.mem_singleton] at bound
    omega
  · apply NatAssign.code_tapeBound_le InverseDescriptor.plan InverseDescriptor.ids 1123
      InverseDescriptor.plan_valid (by decide)
    intro i hi
    simp only [InverseDescriptor.ids,InverseDescriptor.sourceIds,Finset.mem_union,Finset.mem_Icc,
      Finset.mem_insert,Finset.mem_singleton] at hi
    omega

#print axioms tapeBound
end Maxwell.Continuum.Calibration.AllocatedInverse
