import Maxwell.Certificate.LowCompressionWitness.UpperData
namespace Maxwell.Certificate.LowCompressionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperDotCheck_row2 : ∀ j : Fin 28, UpperDotCheck 2 j = true := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
