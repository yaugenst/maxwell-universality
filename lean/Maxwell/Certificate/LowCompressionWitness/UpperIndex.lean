import Maxwell.Certificate.LowCompressionWitness.UpperData
import Maxwell.Certificate.PointInertia.LowCoordinates
namespace Maxwell.Certificate.LowCompressionWitness
open PointInertia
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperLowIndex_mem : ∀ i, (UpperLowIndex i).2 ∈ lowFrequencies := by decide +kernel
theorem UpperLowIndex_injective : Function.Injective UpperLowIndex := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
