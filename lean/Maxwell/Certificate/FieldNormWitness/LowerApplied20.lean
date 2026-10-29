import Maxwell.Certificate.AppliedWitness.LowerApplied20
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied20Rows : Fin 20 → ℤ := ![40589758878084, 226894255843180, 257683930382498, 301631741205268, 356589092769213, 81828209463044, 430708151032954, 433784421206405, 427539621593354, 413705128469673, 85526973889381, 444374336355187, 438152370978409, 423226800013340, 400502750687894, 72841459846448, 306697211449632, 254334882095442, 216805479346444, 195728501122454]
theorem LowerApplied20X0 : highNormUpperX LowerApplied20 0 = LowerApplied20Rows 0 := by decide +kernel
theorem LowerApplied20X1 : highNormUpperX LowerApplied20 1 = LowerApplied20Rows 1 := by decide +kernel
theorem LowerApplied20X2 : highNormUpperX LowerApplied20 2 = LowerApplied20Rows 2 := by decide +kernel
theorem LowerApplied20X3 : highNormUpperX LowerApplied20 3 = LowerApplied20Rows 3 := by decide +kernel
theorem LowerApplied20X4 : highNormUpperX LowerApplied20 4 = LowerApplied20Rows 4 := by decide +kernel
theorem LowerApplied20X5 : highNormUpperX LowerApplied20 5 = LowerApplied20Rows 5 := by decide +kernel
theorem LowerApplied20X6 : highNormUpperX LowerApplied20 6 = LowerApplied20Rows 6 := by decide +kernel
theorem LowerApplied20X7 : highNormUpperX LowerApplied20 7 = LowerApplied20Rows 7 := by decide +kernel
theorem LowerApplied20X8 : highNormUpperX LowerApplied20 8 = LowerApplied20Rows 8 := by decide +kernel
theorem LowerApplied20X9 : highNormUpperX LowerApplied20 9 = LowerApplied20Rows 9 := by decide +kernel
theorem LowerApplied20X10 : highNormUpperX LowerApplied20 10 = LowerApplied20Rows 10 := by decide +kernel
theorem LowerApplied20X11 : highNormUpperX LowerApplied20 11 = LowerApplied20Rows 11 := by decide +kernel
theorem LowerApplied20X12 : highNormUpperX LowerApplied20 12 = LowerApplied20Rows 12 := by decide +kernel
theorem LowerApplied20X13 : highNormUpperX LowerApplied20 13 = LowerApplied20Rows 13 := by decide +kernel
theorem LowerApplied20X14 : highNormUpperX LowerApplied20 14 = LowerApplied20Rows 14 := by decide +kernel
theorem LowerApplied20X15 : highNormUpperX LowerApplied20 15 = LowerApplied20Rows 15 := by decide +kernel
theorem LowerApplied20X16 : highNormUpperX LowerApplied20 16 = LowerApplied20Rows 16 := by decide +kernel
theorem LowerApplied20X17 : highNormUpperX LowerApplied20 17 = LowerApplied20Rows 17 := by decide +kernel
theorem LowerApplied20X18 : highNormUpperX LowerApplied20 18 = LowerApplied20Rows 18 := by decide +kernel
theorem LowerApplied20X19 : highNormUpperX LowerApplied20 19 = LowerApplied20Rows 19 := by decide +kernel
theorem LowerApplied20_rows (x : Fin 20) : highNormUpperX LowerApplied20 x = LowerApplied20Rows x := by
  fin_cases x
  · exact LowerApplied20X0
  · exact LowerApplied20X1
  · exact LowerApplied20X2
  · exact LowerApplied20X3
  · exact LowerApplied20X4
  · exact LowerApplied20X5
  · exact LowerApplied20X6
  · exact LowerApplied20X7
  · exact LowerApplied20X8
  · exact LowerApplied20X9
  · exact LowerApplied20X10
  · exact LowerApplied20X11
  · exact LowerApplied20X12
  · exact LowerApplied20X13
  · exact LowerApplied20X14
  · exact LowerApplied20X15
  · exact LowerApplied20X16
  · exact LowerApplied20X17
  · exact LowerApplied20X18
  · exact LowerApplied20X19
theorem LowerApplied20_bound : highNormUpper LowerApplied20 ≤ 5809145076628304 :=
  highNormUpper_le_of_rows LowerApplied20 LowerApplied20Rows 5809145076628304 LowerApplied20_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
