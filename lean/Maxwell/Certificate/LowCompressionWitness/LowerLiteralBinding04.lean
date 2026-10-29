import Maxwell.Certificate.LowCompressionWitness.LowerData
import Maxwell.Certificate.ProjectionWitness.LowerResult4
import Maxwell.Certificate.AppliedWitness.LowerApplied4
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem LowerLowField_col4 : ∀ k : Fin 42, LowerLowField k 4 = LowerResult4 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
theorem LowerLowApplied_col4 : ∀ k : Fin 42, LowerLowApplied k 4 = LowerApplied4 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
