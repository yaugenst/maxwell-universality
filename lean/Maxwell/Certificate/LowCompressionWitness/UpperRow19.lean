import Maxwell.Certificate.LowCompressionWitness.UpperData
namespace Maxwell.Certificate.LowCompressionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem UpperDotCheck_row19 : ∀ j : Fin 28, UpperDotCheck 19 j = true := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
