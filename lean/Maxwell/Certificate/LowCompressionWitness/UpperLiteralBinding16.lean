import Maxwell.Certificate.LowCompressionWitness.UpperData
import Maxwell.Certificate.ProjectionWitness.UpperResult16
import Maxwell.Certificate.AppliedWitness.UpperApplied16
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperLowField_col16 : ∀ k : Fin 42, UpperLowField k 16 = UpperResult16 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
theorem UpperLowApplied_col16 : ∀ k : Fin 42, UpperLowApplied k 16 = UpperApplied16 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
