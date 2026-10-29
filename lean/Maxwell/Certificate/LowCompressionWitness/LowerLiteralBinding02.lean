import Maxwell.Certificate.LowCompressionWitness.LowerData
import Maxwell.Certificate.ProjectionWitness.LowerResult2
import Maxwell.Certificate.AppliedWitness.LowerApplied2
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem LowerLowField_col2 : ∀ k : Fin 42, LowerLowField k 2 = LowerResult2 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
theorem LowerLowApplied_col2 : ∀ k : Fin 42, LowerLowApplied k 2 = LowerApplied2 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
