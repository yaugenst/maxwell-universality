import Maxwell.Certificate.LowCompressionWitness.UpperData
import Maxwell.Certificate.ProjectionWitness.UpperResult18
import Maxwell.Certificate.AppliedWitness.UpperApplied18
namespace Maxwell.Certificate.LowCompressionWitness
open ProjectionWitness AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperLowField_col18 : ∀ k : Fin 42, UpperLowField k 18 = UpperResult18 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
theorem UpperLowApplied_col18 : ∀ k : Fin 42, UpperLowApplied k 18 = UpperApplied18 (UpperLowIndex k).2 (UpperLowIndex k).1 := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
