import Maxwell.Certificate.AppliedWitness.UpperApplied26
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied26Rows : Fin 20 → ℤ := ![15043867734905, 83472205138088, 95280059797020, 111531937019782, 131189728337213, 30329038034249, 158468307810705, 160411780923268, 158101953378122, 152211951536146, 31699824467515, 163498759423088, 162027299393210, 156506859159229, 147350235739154, 26997864770145, 112829860409416, 94040858094582, 80163781406248, 72006801392780]
theorem UpperApplied26X0 : highNormUpperX UpperApplied26 0 = UpperApplied26Rows 0 := by decide +kernel
theorem UpperApplied26X1 : highNormUpperX UpperApplied26 1 = UpperApplied26Rows 1 := by decide +kernel
theorem UpperApplied26X2 : highNormUpperX UpperApplied26 2 = UpperApplied26Rows 2 := by decide +kernel
theorem UpperApplied26X3 : highNormUpperX UpperApplied26 3 = UpperApplied26Rows 3 := by decide +kernel
theorem UpperApplied26X4 : highNormUpperX UpperApplied26 4 = UpperApplied26Rows 4 := by decide +kernel
theorem UpperApplied26X5 : highNormUpperX UpperApplied26 5 = UpperApplied26Rows 5 := by decide +kernel
theorem UpperApplied26X6 : highNormUpperX UpperApplied26 6 = UpperApplied26Rows 6 := by decide +kernel
theorem UpperApplied26X7 : highNormUpperX UpperApplied26 7 = UpperApplied26Rows 7 := by decide +kernel
theorem UpperApplied26X8 : highNormUpperX UpperApplied26 8 = UpperApplied26Rows 8 := by decide +kernel
theorem UpperApplied26X9 : highNormUpperX UpperApplied26 9 = UpperApplied26Rows 9 := by decide +kernel
theorem UpperApplied26X10 : highNormUpperX UpperApplied26 10 = UpperApplied26Rows 10 := by decide +kernel
theorem UpperApplied26X11 : highNormUpperX UpperApplied26 11 = UpperApplied26Rows 11 := by decide +kernel
theorem UpperApplied26X12 : highNormUpperX UpperApplied26 12 = UpperApplied26Rows 12 := by decide +kernel
theorem UpperApplied26X13 : highNormUpperX UpperApplied26 13 = UpperApplied26Rows 13 := by decide +kernel
theorem UpperApplied26X14 : highNormUpperX UpperApplied26 14 = UpperApplied26Rows 14 := by decide +kernel
theorem UpperApplied26X15 : highNormUpperX UpperApplied26 15 = UpperApplied26Rows 15 := by decide +kernel
theorem UpperApplied26X16 : highNormUpperX UpperApplied26 16 = UpperApplied26Rows 16 := by decide +kernel
theorem UpperApplied26X17 : highNormUpperX UpperApplied26 17 = UpperApplied26Rows 17 := by decide +kernel
theorem UpperApplied26X18 : highNormUpperX UpperApplied26 18 = UpperApplied26Rows 18 := by decide +kernel
theorem UpperApplied26X19 : highNormUpperX UpperApplied26 19 = UpperApplied26Rows 19 := by decide +kernel
theorem UpperApplied26_rows (x : Fin 20) : highNormUpperX UpperApplied26 x = UpperApplied26Rows x := by
  fin_cases x
  · exact UpperApplied26X0
  · exact UpperApplied26X1
  · exact UpperApplied26X2
  · exact UpperApplied26X3
  · exact UpperApplied26X4
  · exact UpperApplied26X5
  · exact UpperApplied26X6
  · exact UpperApplied26X7
  · exact UpperApplied26X8
  · exact UpperApplied26X9
  · exact UpperApplied26X10
  · exact UpperApplied26X11
  · exact UpperApplied26X12
  · exact UpperApplied26X13
  · exact UpperApplied26X14
  · exact UpperApplied26X15
  · exact UpperApplied26X16
  · exact UpperApplied26X17
  · exact UpperApplied26X18
  · exact UpperApplied26X19
theorem UpperApplied26_bound : highNormUpper UpperApplied26 ≤ 2143162973964865 :=
  highNormUpper_le_of_rows UpperApplied26 UpperApplied26Rows 2143162973964865 UpperApplied26_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
