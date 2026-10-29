import Maxwell.Certificate.AppliedWitness.UpperApplied25
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied25Rows : Fin 20 → ℤ := ![14834403525971, 82302932583672, 93947474104284, 109971418314068, 129352634115386, 29906394167478, 156249651124030, 158167406773047, 155889550270086, 150080478887705, 31257577637891, 161209049077473, 159760338517302, 154316939857419, 145287832258687, 26621366150315, 111248688011505, 92725399230074, 79041955807765, 70999691897224]
theorem UpperApplied25X0 : highNormUpperX UpperApplied25 0 = UpperApplied25Rows 0 := by decide +kernel
theorem UpperApplied25X1 : highNormUpperX UpperApplied25 1 = UpperApplied25Rows 1 := by decide +kernel
theorem UpperApplied25X2 : highNormUpperX UpperApplied25 2 = UpperApplied25Rows 2 := by decide +kernel
theorem UpperApplied25X3 : highNormUpperX UpperApplied25 3 = UpperApplied25Rows 3 := by decide +kernel
theorem UpperApplied25X4 : highNormUpperX UpperApplied25 4 = UpperApplied25Rows 4 := by decide +kernel
theorem UpperApplied25X5 : highNormUpperX UpperApplied25 5 = UpperApplied25Rows 5 := by decide +kernel
theorem UpperApplied25X6 : highNormUpperX UpperApplied25 6 = UpperApplied25Rows 6 := by decide +kernel
theorem UpperApplied25X7 : highNormUpperX UpperApplied25 7 = UpperApplied25Rows 7 := by decide +kernel
theorem UpperApplied25X8 : highNormUpperX UpperApplied25 8 = UpperApplied25Rows 8 := by decide +kernel
theorem UpperApplied25X9 : highNormUpperX UpperApplied25 9 = UpperApplied25Rows 9 := by decide +kernel
theorem UpperApplied25X10 : highNormUpperX UpperApplied25 10 = UpperApplied25Rows 10 := by decide +kernel
theorem UpperApplied25X11 : highNormUpperX UpperApplied25 11 = UpperApplied25Rows 11 := by decide +kernel
theorem UpperApplied25X12 : highNormUpperX UpperApplied25 12 = UpperApplied25Rows 12 := by decide +kernel
theorem UpperApplied25X13 : highNormUpperX UpperApplied25 13 = UpperApplied25Rows 13 := by decide +kernel
theorem UpperApplied25X14 : highNormUpperX UpperApplied25 14 = UpperApplied25Rows 14 := by decide +kernel
theorem UpperApplied25X15 : highNormUpperX UpperApplied25 15 = UpperApplied25Rows 15 := by decide +kernel
theorem UpperApplied25X16 : highNormUpperX UpperApplied25 16 = UpperApplied25Rows 16 := by decide +kernel
theorem UpperApplied25X17 : highNormUpperX UpperApplied25 17 = UpperApplied25Rows 17 := by decide +kernel
theorem UpperApplied25X18 : highNormUpperX UpperApplied25 18 = UpperApplied25Rows 18 := by decide +kernel
theorem UpperApplied25X19 : highNormUpperX UpperApplied25 19 = UpperApplied25Rows 19 := by decide +kernel
theorem UpperApplied25_rows (x : Fin 20) : highNormUpperX UpperApplied25 x = UpperApplied25Rows x := by
  fin_cases x
  · exact UpperApplied25X0
  · exact UpperApplied25X1
  · exact UpperApplied25X2
  · exact UpperApplied25X3
  · exact UpperApplied25X4
  · exact UpperApplied25X5
  · exact UpperApplied25X6
  · exact UpperApplied25X7
  · exact UpperApplied25X8
  · exact UpperApplied25X9
  · exact UpperApplied25X10
  · exact UpperApplied25X11
  · exact UpperApplied25X12
  · exact UpperApplied25X13
  · exact UpperApplied25X14
  · exact UpperApplied25X15
  · exact UpperApplied25X16
  · exact UpperApplied25X17
  · exact UpperApplied25X18
  · exact UpperApplied25X19
theorem UpperApplied25_bound : highNormUpper UpperApplied25 ≤ 2113171182311382 :=
  highNormUpper_le_of_rows UpperApplied25 UpperApplied25Rows 2113171182311382 UpperApplied25_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
