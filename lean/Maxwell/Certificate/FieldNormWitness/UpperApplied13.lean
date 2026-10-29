import Maxwell.Certificate.AppliedWitness.UpperApplied13
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied13Rows : Fin 20 → ℤ := ![15041317445067, 83447363162248, 95252679343464, 111504157794432, 131166966823098, 30326738155856, 158452876199029, 160394136765495, 158082066083358, 152192540387268, 31697069968005, 163481804409952, 162009366326192, 156487771966659, 147332619910420, 26994180226434, 112804686074137, 94013669650409, 80138738023366, 71991031768611]
theorem UpperApplied13X0 : highNormUpperX UpperApplied13 0 = UpperApplied13Rows 0 := by decide +kernel
theorem UpperApplied13X1 : highNormUpperX UpperApplied13 1 = UpperApplied13Rows 1 := by decide +kernel
theorem UpperApplied13X2 : highNormUpperX UpperApplied13 2 = UpperApplied13Rows 2 := by decide +kernel
theorem UpperApplied13X3 : highNormUpperX UpperApplied13 3 = UpperApplied13Rows 3 := by decide +kernel
theorem UpperApplied13X4 : highNormUpperX UpperApplied13 4 = UpperApplied13Rows 4 := by decide +kernel
theorem UpperApplied13X5 : highNormUpperX UpperApplied13 5 = UpperApplied13Rows 5 := by decide +kernel
theorem UpperApplied13X6 : highNormUpperX UpperApplied13 6 = UpperApplied13Rows 6 := by decide +kernel
theorem UpperApplied13X7 : highNormUpperX UpperApplied13 7 = UpperApplied13Rows 7 := by decide +kernel
theorem UpperApplied13X8 : highNormUpperX UpperApplied13 8 = UpperApplied13Rows 8 := by decide +kernel
theorem UpperApplied13X9 : highNormUpperX UpperApplied13 9 = UpperApplied13Rows 9 := by decide +kernel
theorem UpperApplied13X10 : highNormUpperX UpperApplied13 10 = UpperApplied13Rows 10 := by decide +kernel
theorem UpperApplied13X11 : highNormUpperX UpperApplied13 11 = UpperApplied13Rows 11 := by decide +kernel
theorem UpperApplied13X12 : highNormUpperX UpperApplied13 12 = UpperApplied13Rows 12 := by decide +kernel
theorem UpperApplied13X13 : highNormUpperX UpperApplied13 13 = UpperApplied13Rows 13 := by decide +kernel
theorem UpperApplied13X14 : highNormUpperX UpperApplied13 14 = UpperApplied13Rows 14 := by decide +kernel
theorem UpperApplied13X15 : highNormUpperX UpperApplied13 15 = UpperApplied13Rows 15 := by decide +kernel
theorem UpperApplied13X16 : highNormUpperX UpperApplied13 16 = UpperApplied13Rows 16 := by decide +kernel
theorem UpperApplied13X17 : highNormUpperX UpperApplied13 17 = UpperApplied13Rows 17 := by decide +kernel
theorem UpperApplied13X18 : highNormUpperX UpperApplied13 18 = UpperApplied13Rows 18 := by decide +kernel
theorem UpperApplied13X19 : highNormUpperX UpperApplied13 19 = UpperApplied13Rows 19 := by decide +kernel
theorem UpperApplied13_rows (x : Fin 20) : highNormUpperX UpperApplied13 x = UpperApplied13Rows x := by
  fin_cases x
  · exact UpperApplied13X0
  · exact UpperApplied13X1
  · exact UpperApplied13X2
  · exact UpperApplied13X3
  · exact UpperApplied13X4
  · exact UpperApplied13X5
  · exact UpperApplied13X6
  · exact UpperApplied13X7
  · exact UpperApplied13X8
  · exact UpperApplied13X9
  · exact UpperApplied13X10
  · exact UpperApplied13X11
  · exact UpperApplied13X12
  · exact UpperApplied13X13
  · exact UpperApplied13X14
  · exact UpperApplied13X15
  · exact UpperApplied13X16
  · exact UpperApplied13X17
  · exact UpperApplied13X18
  · exact UpperApplied13X19
theorem UpperApplied13_bound : highNormUpper UpperApplied13 ≤ 2142811780483500 :=
  highNormUpper_le_of_rows UpperApplied13 UpperApplied13Rows 2142811780483500 UpperApplied13_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
