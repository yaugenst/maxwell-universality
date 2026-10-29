import Maxwell.Certificate.LowCompressionWitness.UpperData
namespace Maxwell.Certificate.LowCompressionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperDotCheck_row0 : ∀ j : Fin 28, UpperDotCheck 0 j = true := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
