import Maxwell.Certificate.ProjectionWitness.UpperResult23
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField23Rows : Fin 20 → ℤ := ![18294104650621609427877507243440, 9755482919031809686788621383812, 19274924108006025288316036103359, 1021451917726619201160854496887, 290968274279572867645752672484, 126516423382114872014506064642, 33587940193647839511769715614, 23440793611082582628268448669, 6505248607692944505794042139, 4682201542099556925168131684, 4682201542099859114103853312, 6505248607693436550035517175, 23440793611083634402623323142, 33587940193649742979499653328, 126516423382117921720145685033, 290968274279590593905074881850, 1021451917726649209083870498196, 19274924108007354207568777212442, 9755482919032192931452385177177, 18294104650623090223458847757996]
theorem UpperField23X0 : highNormUpperX UpperResult23 0 = UpperField23Rows 0 := by decide +kernel
theorem UpperField23X1 : highNormUpperX UpperResult23 1 = UpperField23Rows 1 := by decide +kernel
theorem UpperField23X2 : highNormUpperX UpperResult23 2 = UpperField23Rows 2 := by decide +kernel
theorem UpperField23X3 : highNormUpperX UpperResult23 3 = UpperField23Rows 3 := by decide +kernel
theorem UpperField23X4 : highNormUpperX UpperResult23 4 = UpperField23Rows 4 := by decide +kernel
theorem UpperField23X5 : highNormUpperX UpperResult23 5 = UpperField23Rows 5 := by decide +kernel
theorem UpperField23X6 : highNormUpperX UpperResult23 6 = UpperField23Rows 6 := by decide +kernel
theorem UpperField23X7 : highNormUpperX UpperResult23 7 = UpperField23Rows 7 := by decide +kernel
theorem UpperField23X8 : highNormUpperX UpperResult23 8 = UpperField23Rows 8 := by decide +kernel
theorem UpperField23X9 : highNormUpperX UpperResult23 9 = UpperField23Rows 9 := by decide +kernel
theorem UpperField23X10 : highNormUpperX UpperResult23 10 = UpperField23Rows 10 := by decide +kernel
theorem UpperField23X11 : highNormUpperX UpperResult23 11 = UpperField23Rows 11 := by decide +kernel
theorem UpperField23X12 : highNormUpperX UpperResult23 12 = UpperField23Rows 12 := by decide +kernel
theorem UpperField23X13 : highNormUpperX UpperResult23 13 = UpperField23Rows 13 := by decide +kernel
theorem UpperField23X14 : highNormUpperX UpperResult23 14 = UpperField23Rows 14 := by decide +kernel
theorem UpperField23X15 : highNormUpperX UpperResult23 15 = UpperField23Rows 15 := by decide +kernel
theorem UpperField23X16 : highNormUpperX UpperResult23 16 = UpperField23Rows 16 := by decide +kernel
theorem UpperField23X17 : highNormUpperX UpperResult23 17 = UpperField23Rows 17 := by decide +kernel
theorem UpperField23X18 : highNormUpperX UpperResult23 18 = UpperField23Rows 18 := by decide +kernel
theorem UpperField23X19 : highNormUpperX UpperResult23 19 = UpperField23Rows 19 := by decide +kernel
theorem UpperField23_rows (x : Fin 20) : highNormUpperX UpperResult23 x = UpperField23Rows x := by
  fin_cases x
  · exact UpperField23X0
  · exact UpperField23X1
  · exact UpperField23X2
  · exact UpperField23X3
  · exact UpperField23X4
  · exact UpperField23X5
  · exact UpperField23X6
  · exact UpperField23X7
  · exact UpperField23X8
  · exact UpperField23X9
  · exact UpperField23X10
  · exact UpperField23X11
  · exact UpperField23X12
  · exact UpperField23X13
  · exact UpperField23X14
  · exact UpperField23X15
  · exact UpperField23X16
  · exact UpperField23X17
  · exact UpperField23X18
  · exact UpperField23X19
theorem UpperField23_bound : highNormUpper UpperResult23 ≤ 97663328954007796027609641862381 :=
  highNormUpper_le_of_rows UpperResult23 UpperField23Rows 97663328954007796027609641862381 UpperField23_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
