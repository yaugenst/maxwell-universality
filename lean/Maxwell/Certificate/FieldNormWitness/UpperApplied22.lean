import Maxwell.Certificate.AppliedWitness.UpperApplied22
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied22Rows : Fin 20 → ℤ := ![15014423363381, 83307425426719, 95090684395955, 111313448933727, 130942941924321, 30272182035560, 158176489826719, 160108675905092, 157803742892976, 151928167720802, 31640183977219, 163196545705134, 161721465556641, 156211280194947, 147077183163787, 26946573222036, 112613466976380, 93854214005781, 80004799756483, 71868653524081]
theorem UpperApplied22X0 : highNormUpperX UpperApplied22 0 = UpperApplied22Rows 0 := by decide +kernel
theorem UpperApplied22X1 : highNormUpperX UpperApplied22 1 = UpperApplied22Rows 1 := by decide +kernel
theorem UpperApplied22X2 : highNormUpperX UpperApplied22 2 = UpperApplied22Rows 2 := by decide +kernel
theorem UpperApplied22X3 : highNormUpperX UpperApplied22 3 = UpperApplied22Rows 3 := by decide +kernel
theorem UpperApplied22X4 : highNormUpperX UpperApplied22 4 = UpperApplied22Rows 4 := by decide +kernel
theorem UpperApplied22X5 : highNormUpperX UpperApplied22 5 = UpperApplied22Rows 5 := by decide +kernel
theorem UpperApplied22X6 : highNormUpperX UpperApplied22 6 = UpperApplied22Rows 6 := by decide +kernel
theorem UpperApplied22X7 : highNormUpperX UpperApplied22 7 = UpperApplied22Rows 7 := by decide +kernel
theorem UpperApplied22X8 : highNormUpperX UpperApplied22 8 = UpperApplied22Rows 8 := by decide +kernel
theorem UpperApplied22X9 : highNormUpperX UpperApplied22 9 = UpperApplied22Rows 9 := by decide +kernel
theorem UpperApplied22X10 : highNormUpperX UpperApplied22 10 = UpperApplied22Rows 10 := by decide +kernel
theorem UpperApplied22X11 : highNormUpperX UpperApplied22 11 = UpperApplied22Rows 11 := by decide +kernel
theorem UpperApplied22X12 : highNormUpperX UpperApplied22 12 = UpperApplied22Rows 12 := by decide +kernel
theorem UpperApplied22X13 : highNormUpperX UpperApplied22 13 = UpperApplied22Rows 13 := by decide +kernel
theorem UpperApplied22X14 : highNormUpperX UpperApplied22 14 = UpperApplied22Rows 14 := by decide +kernel
theorem UpperApplied22X15 : highNormUpperX UpperApplied22 15 = UpperApplied22Rows 15 := by decide +kernel
theorem UpperApplied22X16 : highNormUpperX UpperApplied22 16 = UpperApplied22Rows 16 := by decide +kernel
theorem UpperApplied22X17 : highNormUpperX UpperApplied22 17 = UpperApplied22Rows 17 := by decide +kernel
theorem UpperApplied22X18 : highNormUpperX UpperApplied22 18 = UpperApplied22Rows 18 := by decide +kernel
theorem UpperApplied22X19 : highNormUpperX UpperApplied22 19 = UpperApplied22Rows 19 := by decide +kernel
theorem UpperApplied22_rows (x : Fin 20) : highNormUpperX UpperApplied22 x = UpperApplied22Rows x := by
  fin_cases x
  · exact UpperApplied22X0
  · exact UpperApplied22X1
  · exact UpperApplied22X2
  · exact UpperApplied22X3
  · exact UpperApplied22X4
  · exact UpperApplied22X5
  · exact UpperApplied22X6
  · exact UpperApplied22X7
  · exact UpperApplied22X8
  · exact UpperApplied22X9
  · exact UpperApplied22X10
  · exact UpperApplied22X11
  · exact UpperApplied22X12
  · exact UpperApplied22X13
  · exact UpperApplied22X14
  · exact UpperApplied22X15
  · exact UpperApplied22X16
  · exact UpperApplied22X17
  · exact UpperApplied22X18
  · exact UpperApplied22X19
theorem UpperApplied22_bound : highNormUpper UpperApplied22 ≤ 2139092548507741 :=
  highNormUpper_le_of_rows UpperApplied22 UpperApplied22Rows 2139092548507741 UpperApplied22_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
