import Maxwell.Certificate.AppliedWitness.UpperApplied20
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied20Rows : Fin 20 → ℤ := ![15001660521285, 83228426422512, 95004761887447, 111216214119019, 130829600092093, 30248818987062, 158049052753104, 159988800359178, 157682763825183, 151801587264545, 31615673768600, 163064785915153, 161599864020295, 156091710473786, 146954918249459, 26924943264949, 112510672879395, 93768980409593, 79930228901236, 71801837700003]
theorem UpperApplied20X0 : highNormUpperX UpperApplied20 0 = UpperApplied20Rows 0 := by decide +kernel
theorem UpperApplied20X1 : highNormUpperX UpperApplied20 1 = UpperApplied20Rows 1 := by decide +kernel
theorem UpperApplied20X2 : highNormUpperX UpperApplied20 2 = UpperApplied20Rows 2 := by decide +kernel
theorem UpperApplied20X3 : highNormUpperX UpperApplied20 3 = UpperApplied20Rows 3 := by decide +kernel
theorem UpperApplied20X4 : highNormUpperX UpperApplied20 4 = UpperApplied20Rows 4 := by decide +kernel
theorem UpperApplied20X5 : highNormUpperX UpperApplied20 5 = UpperApplied20Rows 5 := by decide +kernel
theorem UpperApplied20X6 : highNormUpperX UpperApplied20 6 = UpperApplied20Rows 6 := by decide +kernel
theorem UpperApplied20X7 : highNormUpperX UpperApplied20 7 = UpperApplied20Rows 7 := by decide +kernel
theorem UpperApplied20X8 : highNormUpperX UpperApplied20 8 = UpperApplied20Rows 8 := by decide +kernel
theorem UpperApplied20X9 : highNormUpperX UpperApplied20 9 = UpperApplied20Rows 9 := by decide +kernel
theorem UpperApplied20X10 : highNormUpperX UpperApplied20 10 = UpperApplied20Rows 10 := by decide +kernel
theorem UpperApplied20X11 : highNormUpperX UpperApplied20 11 = UpperApplied20Rows 11 := by decide +kernel
theorem UpperApplied20X12 : highNormUpperX UpperApplied20 12 = UpperApplied20Rows 12 := by decide +kernel
theorem UpperApplied20X13 : highNormUpperX UpperApplied20 13 = UpperApplied20Rows 13 := by decide +kernel
theorem UpperApplied20X14 : highNormUpperX UpperApplied20 14 = UpperApplied20Rows 14 := by decide +kernel
theorem UpperApplied20X15 : highNormUpperX UpperApplied20 15 = UpperApplied20Rows 15 := by decide +kernel
theorem UpperApplied20X16 : highNormUpperX UpperApplied20 16 = UpperApplied20Rows 16 := by decide +kernel
theorem UpperApplied20X17 : highNormUpperX UpperApplied20 17 = UpperApplied20Rows 17 := by decide +kernel
theorem UpperApplied20X18 : highNormUpperX UpperApplied20 18 = UpperApplied20Rows 18 := by decide +kernel
theorem UpperApplied20X19 : highNormUpperX UpperApplied20 19 = UpperApplied20Rows 19 := by decide +kernel
theorem UpperApplied20_rows (x : Fin 20) : highNormUpperX UpperApplied20 x = UpperApplied20Rows x := by
  fin_cases x
  · exact UpperApplied20X0
  · exact UpperApplied20X1
  · exact UpperApplied20X2
  · exact UpperApplied20X3
  · exact UpperApplied20X4
  · exact UpperApplied20X5
  · exact UpperApplied20X6
  · exact UpperApplied20X7
  · exact UpperApplied20X8
  · exact UpperApplied20X9
  · exact UpperApplied20X10
  · exact UpperApplied20X11
  · exact UpperApplied20X12
  · exact UpperApplied20X13
  · exact UpperApplied20X14
  · exact UpperApplied20X15
  · exact UpperApplied20X16
  · exact UpperApplied20X17
  · exact UpperApplied20X18
  · exact UpperApplied20X19
theorem UpperApplied20_bound : highNormUpper UpperApplied20 ≤ 2137315301813897 :=
  highNormUpper_le_of_rows UpperApplied20 UpperApplied20Rows 2137315301813897 UpperApplied20_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
