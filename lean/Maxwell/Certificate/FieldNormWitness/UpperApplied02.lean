import Maxwell.Certificate.AppliedWitness.UpperApplied2
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied02Rows : Fin 20 → ℤ := ![15837220736777, 87858969301543, 100288069774953, 117408993433495, 138128481802877, 31935428781998, 166879304764330, 168924619447546, 166486732333461, 160279113104019, 33377280567254, 172175075752104, 170625495922529, 164807701884486, 155162875726743, 28424374820520, 118777460827728, 98983336760454, 84374174398294, 75804836537798]
theorem UpperApplied02X0 : highNormUpperX UpperApplied2 0 = UpperApplied02Rows 0 := by decide +kernel
theorem UpperApplied02X1 : highNormUpperX UpperApplied2 1 = UpperApplied02Rows 1 := by decide +kernel
theorem UpperApplied02X2 : highNormUpperX UpperApplied2 2 = UpperApplied02Rows 2 := by decide +kernel
theorem UpperApplied02X3 : highNormUpperX UpperApplied2 3 = UpperApplied02Rows 3 := by decide +kernel
theorem UpperApplied02X4 : highNormUpperX UpperApplied2 4 = UpperApplied02Rows 4 := by decide +kernel
theorem UpperApplied02X5 : highNormUpperX UpperApplied2 5 = UpperApplied02Rows 5 := by decide +kernel
theorem UpperApplied02X6 : highNormUpperX UpperApplied2 6 = UpperApplied02Rows 6 := by decide +kernel
theorem UpperApplied02X7 : highNormUpperX UpperApplied2 7 = UpperApplied02Rows 7 := by decide +kernel
theorem UpperApplied02X8 : highNormUpperX UpperApplied2 8 = UpperApplied02Rows 8 := by decide +kernel
theorem UpperApplied02X9 : highNormUpperX UpperApplied2 9 = UpperApplied02Rows 9 := by decide +kernel
theorem UpperApplied02X10 : highNormUpperX UpperApplied2 10 = UpperApplied02Rows 10 := by decide +kernel
theorem UpperApplied02X11 : highNormUpperX UpperApplied2 11 = UpperApplied02Rows 11 := by decide +kernel
theorem UpperApplied02X12 : highNormUpperX UpperApplied2 12 = UpperApplied02Rows 12 := by decide +kernel
theorem UpperApplied02X13 : highNormUpperX UpperApplied2 13 = UpperApplied02Rows 13 := by decide +kernel
theorem UpperApplied02X14 : highNormUpperX UpperApplied2 14 = UpperApplied02Rows 14 := by decide +kernel
theorem UpperApplied02X15 : highNormUpperX UpperApplied2 15 = UpperApplied02Rows 15 := by decide +kernel
theorem UpperApplied02X16 : highNormUpperX UpperApplied2 16 = UpperApplied02Rows 16 := by decide +kernel
theorem UpperApplied02X17 : highNormUpperX UpperApplied2 17 = UpperApplied02Rows 17 := by decide +kernel
theorem UpperApplied02X18 : highNormUpperX UpperApplied2 18 = UpperApplied02Rows 18 := by decide +kernel
theorem UpperApplied02X19 : highNormUpperX UpperApplied2 19 = UpperApplied02Rows 19 := by decide +kernel
theorem UpperApplied02_rows (x : Fin 20) : highNormUpperX UpperApplied2 x = UpperApplied02Rows x := by
  fin_cases x
  · exact UpperApplied02X0
  · exact UpperApplied02X1
  · exact UpperApplied02X2
  · exact UpperApplied02X3
  · exact UpperApplied02X4
  · exact UpperApplied02X5
  · exact UpperApplied02X6
  · exact UpperApplied02X7
  · exact UpperApplied02X8
  · exact UpperApplied02X9
  · exact UpperApplied02X10
  · exact UpperApplied02X11
  · exact UpperApplied02X12
  · exact UpperApplied02X13
  · exact UpperApplied02X14
  · exact UpperApplied02X15
  · exact UpperApplied02X16
  · exact UpperApplied02X17
  · exact UpperApplied02X18
  · exact UpperApplied02X19
theorem UpperApplied02_bound : highNormUpper UpperApplied2 ≤ 2256539546678909 :=
  highNormUpper_le_of_rows UpperApplied2 UpperApplied02Rows 2256539546678909 UpperApplied02_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
