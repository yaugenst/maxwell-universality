import Maxwell.Certificate.AppliedWitness.LowerApplied13
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied13Rows : Fin 20 → ℤ := ![40091779050415, 224093718969790, 254508231571344, 297925169968849, 352225718967932, 80832676803078, 425468767992619, 428517690799790, 422339972262683, 408657050606127, 84485930138022, 438964237588977, 432832062128971, 418081189804708, 395618273932061, 71952989405139, 302926396428283, 251199904478672, 214128109970027, 193317065815647]
theorem LowerApplied13X0 : highNormUpperX LowerApplied13 0 = LowerApplied13Rows 0 := by decide +kernel
theorem LowerApplied13X1 : highNormUpperX LowerApplied13 1 = LowerApplied13Rows 1 := by decide +kernel
theorem LowerApplied13X2 : highNormUpperX LowerApplied13 2 = LowerApplied13Rows 2 := by decide +kernel
theorem LowerApplied13X3 : highNormUpperX LowerApplied13 3 = LowerApplied13Rows 3 := by decide +kernel
theorem LowerApplied13X4 : highNormUpperX LowerApplied13 4 = LowerApplied13Rows 4 := by decide +kernel
theorem LowerApplied13X5 : highNormUpperX LowerApplied13 5 = LowerApplied13Rows 5 := by decide +kernel
theorem LowerApplied13X6 : highNormUpperX LowerApplied13 6 = LowerApplied13Rows 6 := by decide +kernel
theorem LowerApplied13X7 : highNormUpperX LowerApplied13 7 = LowerApplied13Rows 7 := by decide +kernel
theorem LowerApplied13X8 : highNormUpperX LowerApplied13 8 = LowerApplied13Rows 8 := by decide +kernel
theorem LowerApplied13X9 : highNormUpperX LowerApplied13 9 = LowerApplied13Rows 9 := by decide +kernel
theorem LowerApplied13X10 : highNormUpperX LowerApplied13 10 = LowerApplied13Rows 10 := by decide +kernel
theorem LowerApplied13X11 : highNormUpperX LowerApplied13 11 = LowerApplied13Rows 11 := by decide +kernel
theorem LowerApplied13X12 : highNormUpperX LowerApplied13 12 = LowerApplied13Rows 12 := by decide +kernel
theorem LowerApplied13X13 : highNormUpperX LowerApplied13 13 = LowerApplied13Rows 13 := by decide +kernel
theorem LowerApplied13X14 : highNormUpperX LowerApplied13 14 = LowerApplied13Rows 14 := by decide +kernel
theorem LowerApplied13X15 : highNormUpperX LowerApplied13 15 = LowerApplied13Rows 15 := by decide +kernel
theorem LowerApplied13X16 : highNormUpperX LowerApplied13 16 = LowerApplied13Rows 16 := by decide +kernel
theorem LowerApplied13X17 : highNormUpperX LowerApplied13 17 = LowerApplied13Rows 17 := by decide +kernel
theorem LowerApplied13X18 : highNormUpperX LowerApplied13 18 = LowerApplied13Rows 18 := by decide +kernel
theorem LowerApplied13X19 : highNormUpperX LowerApplied13 19 = LowerApplied13Rows 19 := by decide +kernel
theorem LowerApplied13_rows (x : Fin 20) : highNormUpperX LowerApplied13 x = LowerApplied13Rows x := by
  fin_cases x
  · exact LowerApplied13X0
  · exact LowerApplied13X1
  · exact LowerApplied13X2
  · exact LowerApplied13X3
  · exact LowerApplied13X4
  · exact LowerApplied13X5
  · exact LowerApplied13X6
  · exact LowerApplied13X7
  · exact LowerApplied13X8
  · exact LowerApplied13X9
  · exact LowerApplied13X10
  · exact LowerApplied13X11
  · exact LowerApplied13X12
  · exact LowerApplied13X13
  · exact LowerApplied13X14
  · exact LowerApplied13X15
  · exact LowerApplied13X16
  · exact LowerApplied13X17
  · exact LowerApplied13X18
  · exact LowerApplied13X19
theorem LowerApplied13_bound : highNormUpper LowerApplied13 ≤ 5738166936683134 :=
  highNormUpper_le_of_rows LowerApplied13 LowerApplied13Rows 5738166936683134 LowerApplied13_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
