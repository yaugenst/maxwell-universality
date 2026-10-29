import Maxwell.Certificate.LowCompressionWitness.LowerData
import Maxwell.Certificate.ProjectionWitness.LowerResult22
import Maxwell.Certificate.AppliedWitness.LowerApplied22
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem LowerLowField_col22 : ∀ k : Fin 42, LowerLowField k 22 = LowerResult22 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
theorem LowerLowApplied_col22 : ∀ k : Fin 42, LowerLowApplied k 22 = LowerApplied22 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
