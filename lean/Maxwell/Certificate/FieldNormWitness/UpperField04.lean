import Maxwell.Certificate.ProjectionWitness.UpperResult4
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField04Rows : Fin 20 → ℤ := ![26540776102007870462533439999834, 14680268208992269233772126098752, 20458397120475959373751628115845, 426173974536071085903156332934, 641369268430839578276391579158, 80382143648816438400046398550, 77821253942872726152542542358, 21578215587806955787654912379, 12569641091626364865169325033, 5489446504312315101631044892, 5489446504312154893887829659, 12569641091626574982224894378, 21578215587807133342882264026, 77821253942872970876601227682, 80382143648816958916756436301, 641369268430835221552284483083, 426173974536077996439610836340, 20458397120475924222107668197003, 14680268208992024379944053750591, 26540776102007804364374883373601]
theorem UpperField04X0 : highNormUpperX UpperResult4 0 = UpperField04Rows 0 := by decide +kernel
theorem UpperField04X1 : highNormUpperX UpperResult4 1 = UpperField04Rows 1 := by decide +kernel
theorem UpperField04X2 : highNormUpperX UpperResult4 2 = UpperField04Rows 2 := by decide +kernel
theorem UpperField04X3 : highNormUpperX UpperResult4 3 = UpperField04Rows 3 := by decide +kernel
theorem UpperField04X4 : highNormUpperX UpperResult4 4 = UpperField04Rows 4 := by decide +kernel
theorem UpperField04X5 : highNormUpperX UpperResult4 5 = UpperField04Rows 5 := by decide +kernel
theorem UpperField04X6 : highNormUpperX UpperResult4 6 = UpperField04Rows 6 := by decide +kernel
theorem UpperField04X7 : highNormUpperX UpperResult4 7 = UpperField04Rows 7 := by decide +kernel
theorem UpperField04X8 : highNormUpperX UpperResult4 8 = UpperField04Rows 8 := by decide +kernel
theorem UpperField04X9 : highNormUpperX UpperResult4 9 = UpperField04Rows 9 := by decide +kernel
theorem UpperField04X10 : highNormUpperX UpperResult4 10 = UpperField04Rows 10 := by decide +kernel
theorem UpperField04X11 : highNormUpperX UpperResult4 11 = UpperField04Rows 11 := by decide +kernel
theorem UpperField04X12 : highNormUpperX UpperResult4 12 = UpperField04Rows 12 := by decide +kernel
theorem UpperField04X13 : highNormUpperX UpperResult4 13 = UpperField04Rows 13 := by decide +kernel
theorem UpperField04X14 : highNormUpperX UpperResult4 14 = UpperField04Rows 14 := by decide +kernel
theorem UpperField04X15 : highNormUpperX UpperResult4 15 = UpperField04Rows 15 := by decide +kernel
theorem UpperField04X16 : highNormUpperX UpperResult4 16 = UpperField04Rows 16 := by decide +kernel
theorem UpperField04X17 : highNormUpperX UpperResult4 17 = UpperField04Rows 17 := by decide +kernel
theorem UpperField04X18 : highNormUpperX UpperResult4 18 = UpperField04Rows 18 := by decide +kernel
theorem UpperField04X19 : highNormUpperX UpperResult4 19 = UpperField04Rows 19 := by decide +kernel
theorem UpperField04_rows (x : Fin 20) : highNormUpperX UpperResult4 x = UpperField04Rows x := by
  fin_cases x
  · exact UpperField04X0
  · exact UpperField04X1
  · exact UpperField04X2
  · exact UpperField04X3
  · exact UpperField04X4
  · exact UpperField04X5
  · exact UpperField04X6
  · exact UpperField04X7
  · exact UpperField04X8
  · exact UpperField04X9
  · exact UpperField04X10
  · exact UpperField04X11
  · exact UpperField04X12
  · exact UpperField04X13
  · exact UpperField04X14
  · exact UpperField04X15
  · exact UpperField04X16
  · exact UpperField04X17
  · exact UpperField04X18
  · exact UpperField04X19
theorem UpperField04_bound : highNormUpper UpperResult4 ≤ 125889650750436546511974639642399 :=
  highNormUpper_le_of_rows UpperResult4 UpperField04Rows 125889650750436546511974639642399 UpperField04_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
