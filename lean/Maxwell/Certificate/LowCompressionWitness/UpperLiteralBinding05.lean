import Maxwell.Certificate.LowCompressionWitness.UpperData
import Maxwell.Certificate.ProjectionWitness.UpperResult5
import Maxwell.Certificate.AppliedWitness.UpperApplied5
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperLowField_col5 : ∀ k : Fin 42, UpperLowField k 5 = UpperResult5 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
theorem UpperLowApplied_col5 : ∀ k : Fin 42, UpperLowApplied k 5 = UpperApplied5 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
