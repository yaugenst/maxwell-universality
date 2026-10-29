import Maxwell.Certificate.AppliedWitness.UpperApplied14
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied14Rows : Fin 20 → ℤ := ![15083235640880, 83680501355621, 95524006544473, 111832333171790, 131562611740113, 30419692871461, 158956067563050, 160915644652469, 158591855145041, 152664467314082, 31793773109497, 163999347677324, 162535466912298, 156991875922694, 147791330384774, 27074532238191, 113130470866227, 94281082330591, 80365957565955, 72194797307762]
theorem UpperApplied14X0 : highNormUpperX UpperApplied14 0 = UpperApplied14Rows 0 := by decide +kernel
theorem UpperApplied14X1 : highNormUpperX UpperApplied14 1 = UpperApplied14Rows 1 := by decide +kernel
theorem UpperApplied14X2 : highNormUpperX UpperApplied14 2 = UpperApplied14Rows 2 := by decide +kernel
theorem UpperApplied14X3 : highNormUpperX UpperApplied14 3 = UpperApplied14Rows 3 := by decide +kernel
theorem UpperApplied14X4 : highNormUpperX UpperApplied14 4 = UpperApplied14Rows 4 := by decide +kernel
theorem UpperApplied14X5 : highNormUpperX UpperApplied14 5 = UpperApplied14Rows 5 := by decide +kernel
theorem UpperApplied14X6 : highNormUpperX UpperApplied14 6 = UpperApplied14Rows 6 := by decide +kernel
theorem UpperApplied14X7 : highNormUpperX UpperApplied14 7 = UpperApplied14Rows 7 := by decide +kernel
theorem UpperApplied14X8 : highNormUpperX UpperApplied14 8 = UpperApplied14Rows 8 := by decide +kernel
theorem UpperApplied14X9 : highNormUpperX UpperApplied14 9 = UpperApplied14Rows 9 := by decide +kernel
theorem UpperApplied14X10 : highNormUpperX UpperApplied14 10 = UpperApplied14Rows 10 := by decide +kernel
theorem UpperApplied14X11 : highNormUpperX UpperApplied14 11 = UpperApplied14Rows 11 := by decide +kernel
theorem UpperApplied14X12 : highNormUpperX UpperApplied14 12 = UpperApplied14Rows 12 := by decide +kernel
theorem UpperApplied14X13 : highNormUpperX UpperApplied14 13 = UpperApplied14Rows 13 := by decide +kernel
theorem UpperApplied14X14 : highNormUpperX UpperApplied14 14 = UpperApplied14Rows 14 := by decide +kernel
theorem UpperApplied14X15 : highNormUpperX UpperApplied14 15 = UpperApplied14Rows 15 := by decide +kernel
theorem UpperApplied14X16 : highNormUpperX UpperApplied14 16 = UpperApplied14Rows 16 := by decide +kernel
theorem UpperApplied14X17 : highNormUpperX UpperApplied14 17 = UpperApplied14Rows 17 := by decide +kernel
theorem UpperApplied14X18 : highNormUpperX UpperApplied14 18 = UpperApplied14Rows 18 := by decide +kernel
theorem UpperApplied14X19 : highNormUpperX UpperApplied14 19 = UpperApplied14Rows 19 := by decide +kernel
theorem UpperApplied14_rows (x : Fin 20) : highNormUpperX UpperApplied14 x = UpperApplied14Rows x := by
  fin_cases x
  · exact UpperApplied14X0
  · exact UpperApplied14X1
  · exact UpperApplied14X2
  · exact UpperApplied14X3
  · exact UpperApplied14X4
  · exact UpperApplied14X5
  · exact UpperApplied14X6
  · exact UpperApplied14X7
  · exact UpperApplied14X8
  · exact UpperApplied14X9
  · exact UpperApplied14X10
  · exact UpperApplied14X11
  · exact UpperApplied14X12
  · exact UpperApplied14X13
  · exact UpperApplied14X14
  · exact UpperApplied14X15
  · exact UpperApplied14X16
  · exact UpperApplied14X17
  · exact UpperApplied14X18
  · exact UpperApplied14X19
theorem UpperApplied14_bound : highNormUpper UpperApplied14 ≤ 2149389050314293 :=
  highNormUpper_le_of_rows UpperApplied14 UpperApplied14Rows 2149389050314293 UpperApplied14_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
