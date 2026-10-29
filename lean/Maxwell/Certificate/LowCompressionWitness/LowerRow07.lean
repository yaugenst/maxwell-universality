import Maxwell.Certificate.LowCompressionWitness.LowerData
namespace Maxwell.Certificate.LowCompressionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem LowerDotCheck_row7 : ∀ j : Fin 28, LowerDotCheck 7 j = true := by decide +kernel
end Maxwell.Certificate.LowCompressionWitness
