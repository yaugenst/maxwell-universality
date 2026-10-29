import Maxwell.Certificate.AppliedWitness.UpperApplied16
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied16Rows : Fin 20 → ℤ := ![15174958521200, 84194045344511, 96104919682803, 112505972514685, 132348763819556, 30599145070911, 159887952155390, 161848425419424, 159515323716095, 153565669263148, 31981559776224, 164961343870380, 163477879672187, 157906727541214, 148663236317339, 27236210793774, 113816727211105, 94854990507916, 80856400737778, 72634338606346]
theorem UpperApplied16X0 : highNormUpperX UpperApplied16 0 = UpperApplied16Rows 0 := by decide +kernel
theorem UpperApplied16X1 : highNormUpperX UpperApplied16 1 = UpperApplied16Rows 1 := by decide +kernel
theorem UpperApplied16X2 : highNormUpperX UpperApplied16 2 = UpperApplied16Rows 2 := by decide +kernel
theorem UpperApplied16X3 : highNormUpperX UpperApplied16 3 = UpperApplied16Rows 3 := by decide +kernel
theorem UpperApplied16X4 : highNormUpperX UpperApplied16 4 = UpperApplied16Rows 4 := by decide +kernel
theorem UpperApplied16X5 : highNormUpperX UpperApplied16 5 = UpperApplied16Rows 5 := by decide +kernel
theorem UpperApplied16X6 : highNormUpperX UpperApplied16 6 = UpperApplied16Rows 6 := by decide +kernel
theorem UpperApplied16X7 : highNormUpperX UpperApplied16 7 = UpperApplied16Rows 7 := by decide +kernel
theorem UpperApplied16X8 : highNormUpperX UpperApplied16 8 = UpperApplied16Rows 8 := by decide +kernel
theorem UpperApplied16X9 : highNormUpperX UpperApplied16 9 = UpperApplied16Rows 9 := by decide +kernel
theorem UpperApplied16X10 : highNormUpperX UpperApplied16 10 = UpperApplied16Rows 10 := by decide +kernel
theorem UpperApplied16X11 : highNormUpperX UpperApplied16 11 = UpperApplied16Rows 11 := by decide +kernel
theorem UpperApplied16X12 : highNormUpperX UpperApplied16 12 = UpperApplied16Rows 12 := by decide +kernel
theorem UpperApplied16X13 : highNormUpperX UpperApplied16 13 = UpperApplied16Rows 13 := by decide +kernel
theorem UpperApplied16X14 : highNormUpperX UpperApplied16 14 = UpperApplied16Rows 14 := by decide +kernel
theorem UpperApplied16X15 : highNormUpperX UpperApplied16 15 = UpperApplied16Rows 15 := by decide +kernel
theorem UpperApplied16X16 : highNormUpperX UpperApplied16 16 = UpperApplied16Rows 16 := by decide +kernel
theorem UpperApplied16X17 : highNormUpperX UpperApplied16 17 = UpperApplied16Rows 17 := by decide +kernel
theorem UpperApplied16X18 : highNormUpperX UpperApplied16 18 = UpperApplied16Rows 18 := by decide +kernel
theorem UpperApplied16X19 : highNormUpperX UpperApplied16 19 = UpperApplied16Rows 19 := by decide +kernel
theorem UpperApplied16_rows (x : Fin 20) : highNormUpperX UpperApplied16 x = UpperApplied16Rows x := by
  fin_cases x
  · exact UpperApplied16X0
  · exact UpperApplied16X1
  · exact UpperApplied16X2
  · exact UpperApplied16X3
  · exact UpperApplied16X4
  · exact UpperApplied16X5
  · exact UpperApplied16X6
  · exact UpperApplied16X7
  · exact UpperApplied16X8
  · exact UpperApplied16X9
  · exact UpperApplied16X10
  · exact UpperApplied16X11
  · exact UpperApplied16X12
  · exact UpperApplied16X13
  · exact UpperApplied16X14
  · exact UpperApplied16X15
  · exact UpperApplied16X16
  · exact UpperApplied16X17
  · exact UpperApplied16X18
  · exact UpperApplied16X19
theorem UpperApplied16_bound : highNormUpper UpperApplied16 ≤ 2162134590541986 :=
  highNormUpper_le_of_rows UpperApplied16 UpperApplied16Rows 2162134590541986 UpperApplied16_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
