import Maxwell.Certificate.LowCompressionWitness.UpperData
import Maxwell.Certificate.ProjectionWitness.UpperResult27
import Maxwell.Certificate.AppliedWitness.UpperApplied27
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperLowField_col27 : ∀ k : Fin 42, UpperLowField k 27 = UpperResult27 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
theorem UpperLowApplied_col27 : ∀ k : Fin 42, UpperLowApplied k 27 = UpperApplied27 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
