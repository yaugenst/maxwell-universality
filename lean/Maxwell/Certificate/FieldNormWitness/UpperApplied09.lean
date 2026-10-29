import Maxwell.Certificate.AppliedWitness.UpperApplied9
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied09Rows : Fin 20 → ℤ := ![15080400280355, 83664396162158, 95503631950547, 111794792902249, 131500210514111, 30403334348049, 158847786498501, 160798167449872, 158481671623799, 152576632511943, 31777926303652, 163890171988333, 162417582491238, 156882892284980, 147702812098815, 27063192534578, 113094663653849, 94261758141693, 80350467181057, 72178090169473]
theorem UpperApplied09X0 : highNormUpperX UpperApplied9 0 = UpperApplied09Rows 0 := by decide +kernel
theorem UpperApplied09X1 : highNormUpperX UpperApplied9 1 = UpperApplied09Rows 1 := by decide +kernel
theorem UpperApplied09X2 : highNormUpperX UpperApplied9 2 = UpperApplied09Rows 2 := by decide +kernel
theorem UpperApplied09X3 : highNormUpperX UpperApplied9 3 = UpperApplied09Rows 3 := by decide +kernel
theorem UpperApplied09X4 : highNormUpperX UpperApplied9 4 = UpperApplied09Rows 4 := by decide +kernel
theorem UpperApplied09X5 : highNormUpperX UpperApplied9 5 = UpperApplied09Rows 5 := by decide +kernel
theorem UpperApplied09X6 : highNormUpperX UpperApplied9 6 = UpperApplied09Rows 6 := by decide +kernel
theorem UpperApplied09X7 : highNormUpperX UpperApplied9 7 = UpperApplied09Rows 7 := by decide +kernel
theorem UpperApplied09X8 : highNormUpperX UpperApplied9 8 = UpperApplied09Rows 8 := by decide +kernel
theorem UpperApplied09X9 : highNormUpperX UpperApplied9 9 = UpperApplied09Rows 9 := by decide +kernel
theorem UpperApplied09X10 : highNormUpperX UpperApplied9 10 = UpperApplied09Rows 10 := by decide +kernel
theorem UpperApplied09X11 : highNormUpperX UpperApplied9 11 = UpperApplied09Rows 11 := by decide +kernel
theorem UpperApplied09X12 : highNormUpperX UpperApplied9 12 = UpperApplied09Rows 12 := by decide +kernel
theorem UpperApplied09X13 : highNormUpperX UpperApplied9 13 = UpperApplied09Rows 13 := by decide +kernel
theorem UpperApplied09X14 : highNormUpperX UpperApplied9 14 = UpperApplied09Rows 14 := by decide +kernel
theorem UpperApplied09X15 : highNormUpperX UpperApplied9 15 = UpperApplied09Rows 15 := by decide +kernel
theorem UpperApplied09X16 : highNormUpperX UpperApplied9 16 = UpperApplied09Rows 16 := by decide +kernel
theorem UpperApplied09X17 : highNormUpperX UpperApplied9 17 = UpperApplied09Rows 17 := by decide +kernel
theorem UpperApplied09X18 : highNormUpperX UpperApplied9 18 = UpperApplied09Rows 18 := by decide +kernel
theorem UpperApplied09X19 : highNormUpperX UpperApplied9 19 = UpperApplied09Rows 19 := by decide +kernel
theorem UpperApplied09_rows (x : Fin 20) : highNormUpperX UpperApplied9 x = UpperApplied09Rows x := by
  fin_cases x
  · exact UpperApplied09X0
  · exact UpperApplied09X1
  · exact UpperApplied09X2
  · exact UpperApplied09X3
  · exact UpperApplied09X4
  · exact UpperApplied09X5
  · exact UpperApplied09X6
  · exact UpperApplied09X7
  · exact UpperApplied09X8
  · exact UpperApplied09X9
  · exact UpperApplied09X10
  · exact UpperApplied09X11
  · exact UpperApplied09X12
  · exact UpperApplied09X13
  · exact UpperApplied09X14
  · exact UpperApplied09X15
  · exact UpperApplied09X16
  · exact UpperApplied09X17
  · exact UpperApplied09X18
  · exact UpperApplied09X19
theorem UpperApplied09_bound : highNormUpper UpperApplied9 ≤ 2148270581089252 :=
  highNormUpper_le_of_rows UpperApplied9 UpperApplied09Rows 2148270581089252 UpperApplied09_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
