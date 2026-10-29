import Maxwell.Certificate.LowCompressionWitness.LowerData
import Maxwell.Certificate.ProjectionWitness.LowerResult15
import Maxwell.Certificate.AppliedWitness.LowerApplied15
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem LowerLowField_col15 : ∀ k : Fin 42, LowerLowField k 15 = LowerResult15 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
theorem LowerLowApplied_col15 : ∀ k : Fin 42, LowerLowApplied k 15 = LowerApplied15 (LowerLowIndex k).2 (LowerLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
