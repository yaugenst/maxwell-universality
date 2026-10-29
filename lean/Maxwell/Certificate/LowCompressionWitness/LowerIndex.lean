import Maxwell.Certificate.LowCompressionWitness.LowerData
import Maxwell.Certificate.PointInertia.LowCoordinates
namespace Maxwell.Certificate.LowCompressionWitness
open PointInertia
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem LowerLowIndex_mem : ∀ i, (LowerLowIndex i).2 ∈ lowFrequencies := by decide +kernel
theorem LowerLowIndex_injective : Function.Injective LowerLowIndex := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
