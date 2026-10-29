import Maxwell.Certificate.AppliedWitness.UpperApplied1
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied01Rows : Fin 20 → ℤ := ![15129522825268, 83945829480039, 95820180623252, 112165459240528, 131942806917549, 30502843221332, 159379392257025, 161328359472330, 159004612163969, 153088202120834, 31881531827746, 164439232492783, 162953485144799, 157400193221199, 148198267451572, 27152088538483, 113475204526704, 94573954412460, 80616405555751, 72420433722195]
theorem UpperApplied01X0 : highNormUpperX UpperApplied1 0 = UpperApplied01Rows 0 := by decide +kernel
theorem UpperApplied01X1 : highNormUpperX UpperApplied1 1 = UpperApplied01Rows 1 := by decide +kernel
theorem UpperApplied01X2 : highNormUpperX UpperApplied1 2 = UpperApplied01Rows 2 := by decide +kernel
theorem UpperApplied01X3 : highNormUpperX UpperApplied1 3 = UpperApplied01Rows 3 := by decide +kernel
theorem UpperApplied01X4 : highNormUpperX UpperApplied1 4 = UpperApplied01Rows 4 := by decide +kernel
theorem UpperApplied01X5 : highNormUpperX UpperApplied1 5 = UpperApplied01Rows 5 := by decide +kernel
theorem UpperApplied01X6 : highNormUpperX UpperApplied1 6 = UpperApplied01Rows 6 := by decide +kernel
theorem UpperApplied01X7 : highNormUpperX UpperApplied1 7 = UpperApplied01Rows 7 := by decide +kernel
theorem UpperApplied01X8 : highNormUpperX UpperApplied1 8 = UpperApplied01Rows 8 := by decide +kernel
theorem UpperApplied01X9 : highNormUpperX UpperApplied1 9 = UpperApplied01Rows 9 := by decide +kernel
theorem UpperApplied01X10 : highNormUpperX UpperApplied1 10 = UpperApplied01Rows 10 := by decide +kernel
theorem UpperApplied01X11 : highNormUpperX UpperApplied1 11 = UpperApplied01Rows 11 := by decide +kernel
theorem UpperApplied01X12 : highNormUpperX UpperApplied1 12 = UpperApplied01Rows 12 := by decide +kernel
theorem UpperApplied01X13 : highNormUpperX UpperApplied1 13 = UpperApplied01Rows 13 := by decide +kernel
theorem UpperApplied01X14 : highNormUpperX UpperApplied1 14 = UpperApplied01Rows 14 := by decide +kernel
theorem UpperApplied01X15 : highNormUpperX UpperApplied1 15 = UpperApplied01Rows 15 := by decide +kernel
theorem UpperApplied01X16 : highNormUpperX UpperApplied1 16 = UpperApplied01Rows 16 := by decide +kernel
theorem UpperApplied01X17 : highNormUpperX UpperApplied1 17 = UpperApplied01Rows 17 := by decide +kernel
theorem UpperApplied01X18 : highNormUpperX UpperApplied1 18 = UpperApplied01Rows 18 := by decide +kernel
theorem UpperApplied01X19 : highNormUpperX UpperApplied1 19 = UpperApplied01Rows 19 := by decide +kernel
theorem UpperApplied01_rows (x : Fin 20) : highNormUpperX UpperApplied1 x = UpperApplied01Rows x := by
  fin_cases x
  · exact UpperApplied01X0
  · exact UpperApplied01X1
  · exact UpperApplied01X2
  · exact UpperApplied01X3
  · exact UpperApplied01X4
  · exact UpperApplied01X5
  · exact UpperApplied01X6
  · exact UpperApplied01X7
  · exact UpperApplied01X8
  · exact UpperApplied01X9
  · exact UpperApplied01X10
  · exact UpperApplied01X11
  · exact UpperApplied01X12
  · exact UpperApplied01X13
  · exact UpperApplied01X14
  · exact UpperApplied01X15
  · exact UpperApplied01X16
  · exact UpperApplied01X17
  · exact UpperApplied01X18
  · exact UpperApplied01X19
theorem UpperApplied01_bound : highNormUpper UpperApplied1 ≤ 2155418005215818 :=
  highNormUpper_le_of_rows UpperApplied1 UpperApplied01Rows 2155418005215818 UpperApplied01_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
