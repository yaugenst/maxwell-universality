import Maxwell.Certificate.LowCompressionWitness.UpperData
import Maxwell.Certificate.ProjectionWitness.UpperResult22
import Maxwell.Certificate.AppliedWitness.UpperApplied22
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperLowField_col22 : ∀ k : Fin 42, UpperLowField k 22 = UpperResult22 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
theorem UpperLowApplied_col22 : ∀ k : Fin 42, UpperLowApplied k 22 = UpperApplied22 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
