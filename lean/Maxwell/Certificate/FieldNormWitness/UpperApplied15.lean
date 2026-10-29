import Maxwell.Certificate.AppliedWitness.UpperApplied15
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied15Rows : Fin 20 → ℤ := ![14664679811984, 81364584069150, 92873888475835, 108717145377312, 127884315994423, 29565959733687, 154480637759636, 156371420452278, 154120389096055, 148379665560256, 30902257948881, 159384344246530, 157946311844763, 152564733491747, 143640972435616, 26318134520107, 109984764002553, 91666183062242, 78140190996074, 70192353465810]
theorem UpperApplied15X0 : highNormUpperX UpperApplied15 0 = UpperApplied15Rows 0 := by decide +kernel
theorem UpperApplied15X1 : highNormUpperX UpperApplied15 1 = UpperApplied15Rows 1 := by decide +kernel
theorem UpperApplied15X2 : highNormUpperX UpperApplied15 2 = UpperApplied15Rows 2 := by decide +kernel
theorem UpperApplied15X3 : highNormUpperX UpperApplied15 3 = UpperApplied15Rows 3 := by decide +kernel
theorem UpperApplied15X4 : highNormUpperX UpperApplied15 4 = UpperApplied15Rows 4 := by decide +kernel
theorem UpperApplied15X5 : highNormUpperX UpperApplied15 5 = UpperApplied15Rows 5 := by decide +kernel
theorem UpperApplied15X6 : highNormUpperX UpperApplied15 6 = UpperApplied15Rows 6 := by decide +kernel
theorem UpperApplied15X7 : highNormUpperX UpperApplied15 7 = UpperApplied15Rows 7 := by decide +kernel
theorem UpperApplied15X8 : highNormUpperX UpperApplied15 8 = UpperApplied15Rows 8 := by decide +kernel
theorem UpperApplied15X9 : highNormUpperX UpperApplied15 9 = UpperApplied15Rows 9 := by decide +kernel
theorem UpperApplied15X10 : highNormUpperX UpperApplied15 10 = UpperApplied15Rows 10 := by decide +kernel
theorem UpperApplied15X11 : highNormUpperX UpperApplied15 11 = UpperApplied15Rows 11 := by decide +kernel
theorem UpperApplied15X12 : highNormUpperX UpperApplied15 12 = UpperApplied15Rows 12 := by decide +kernel
theorem UpperApplied15X13 : highNormUpperX UpperApplied15 13 = UpperApplied15Rows 13 := by decide +kernel
theorem UpperApplied15X14 : highNormUpperX UpperApplied15 14 = UpperApplied15Rows 14 := by decide +kernel
theorem UpperApplied15X15 : highNormUpperX UpperApplied15 15 = UpperApplied15Rows 15 := by decide +kernel
theorem UpperApplied15X16 : highNormUpperX UpperApplied15 16 = UpperApplied15Rows 16 := by decide +kernel
theorem UpperApplied15X17 : highNormUpperX UpperApplied15 17 = UpperApplied15Rows 17 := by decide +kernel
theorem UpperApplied15X18 : highNormUpperX UpperApplied15 18 = UpperApplied15Rows 18 := by decide +kernel
theorem UpperApplied15X19 : highNormUpperX UpperApplied15 19 = UpperApplied15Rows 19 := by decide +kernel
theorem UpperApplied15_rows (x : Fin 20) : highNormUpperX UpperApplied15 x = UpperApplied15Rows x := by
  fin_cases x
  · exact UpperApplied15X0
  · exact UpperApplied15X1
  · exact UpperApplied15X2
  · exact UpperApplied15X3
  · exact UpperApplied15X4
  · exact UpperApplied15X5
  · exact UpperApplied15X6
  · exact UpperApplied15X7
  · exact UpperApplied15X8
  · exact UpperApplied15X9
  · exact UpperApplied15X10
  · exact UpperApplied15X11
  · exact UpperApplied15X12
  · exact UpperApplied15X13
  · exact UpperApplied15X14
  · exact UpperApplied15X15
  · exact UpperApplied15X16
  · exact UpperApplied15X17
  · exact UpperApplied15X18
  · exact UpperApplied15X19
theorem UpperApplied15_bound : highNormUpper UpperApplied15 ≤ 2089162932344939 :=
  highNormUpper_le_of_rows UpperApplied15 UpperApplied15Rows 2089162932344939 UpperApplied15_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
