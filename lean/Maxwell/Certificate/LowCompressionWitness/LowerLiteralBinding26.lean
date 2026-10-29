import Maxwell.Certificate.LowCompressionWitness.LowerData
import Maxwell.Certificate.ProjectionWitness.LowerResult26
import Maxwell.Certificate.AppliedWitness.LowerApplied26
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem LowerLowField_col26 : ∀ k : Fin 42, LowerLowField k 26 = LowerResult26 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
theorem LowerLowApplied_col26 : ∀ k : Fin 42, LowerLowApplied k 26 = LowerApplied26 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
