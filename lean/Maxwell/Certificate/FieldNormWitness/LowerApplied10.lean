import Maxwell.Certificate.AppliedWitness.LowerApplied10
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied10Rows : Fin 20 → ℤ := ![40837657015199, 228274129568050, 259261402685105, 303475807237115, 358761687165292, 82326294317856, 433335423865126, 436442551632667, 430159286114105, 416229216840547, 86048927575355, 447083015648664, 440837384071019, 425820565711325, 402943717587094, 73285019421007, 308563835542073, 255891582442910, 218130006231409, 196922786111712]
theorem LowerApplied10X0 : highNormUpperX LowerApplied10 0 = LowerApplied10Rows 0 := by decide +kernel
theorem LowerApplied10X1 : highNormUpperX LowerApplied10 1 = LowerApplied10Rows 1 := by decide +kernel
theorem LowerApplied10X2 : highNormUpperX LowerApplied10 2 = LowerApplied10Rows 2 := by decide +kernel
theorem LowerApplied10X3 : highNormUpperX LowerApplied10 3 = LowerApplied10Rows 3 := by decide +kernel
theorem LowerApplied10X4 : highNormUpperX LowerApplied10 4 = LowerApplied10Rows 4 := by decide +kernel
theorem LowerApplied10X5 : highNormUpperX LowerApplied10 5 = LowerApplied10Rows 5 := by decide +kernel
theorem LowerApplied10X6 : highNormUpperX LowerApplied10 6 = LowerApplied10Rows 6 := by decide +kernel
theorem LowerApplied10X7 : highNormUpperX LowerApplied10 7 = LowerApplied10Rows 7 := by decide +kernel
theorem LowerApplied10X8 : highNormUpperX LowerApplied10 8 = LowerApplied10Rows 8 := by decide +kernel
theorem LowerApplied10X9 : highNormUpperX LowerApplied10 9 = LowerApplied10Rows 9 := by decide +kernel
theorem LowerApplied10X10 : highNormUpperX LowerApplied10 10 = LowerApplied10Rows 10 := by decide +kernel
theorem LowerApplied10X11 : highNormUpperX LowerApplied10 11 = LowerApplied10Rows 11 := by decide +kernel
theorem LowerApplied10X12 : highNormUpperX LowerApplied10 12 = LowerApplied10Rows 12 := by decide +kernel
theorem LowerApplied10X13 : highNormUpperX LowerApplied10 13 = LowerApplied10Rows 13 := by decide +kernel
theorem LowerApplied10X14 : highNormUpperX LowerApplied10 14 = LowerApplied10Rows 14 := by decide +kernel
theorem LowerApplied10X15 : highNormUpperX LowerApplied10 15 = LowerApplied10Rows 15 := by decide +kernel
theorem LowerApplied10X16 : highNormUpperX LowerApplied10 16 = LowerApplied10Rows 16 := by decide +kernel
theorem LowerApplied10X17 : highNormUpperX LowerApplied10 17 = LowerApplied10Rows 17 := by decide +kernel
theorem LowerApplied10X18 : highNormUpperX LowerApplied10 18 = LowerApplied10Rows 18 := by decide +kernel
theorem LowerApplied10X19 : highNormUpperX LowerApplied10 19 = LowerApplied10Rows 19 := by decide +kernel
theorem LowerApplied10_rows (x : Fin 20) : highNormUpperX LowerApplied10 x = LowerApplied10Rows x := by
  fin_cases x
  · exact LowerApplied10X0
  · exact LowerApplied10X1
  · exact LowerApplied10X2
  · exact LowerApplied10X3
  · exact LowerApplied10X4
  · exact LowerApplied10X5
  · exact LowerApplied10X6
  · exact LowerApplied10X7
  · exact LowerApplied10X8
  · exact LowerApplied10X9
  · exact LowerApplied10X10
  · exact LowerApplied10X11
  · exact LowerApplied10X12
  · exact LowerApplied10X13
  · exact LowerApplied10X14
  · exact LowerApplied10X15
  · exact LowerApplied10X16
  · exact LowerApplied10X17
  · exact LowerApplied10X18
  · exact LowerApplied10X19
theorem LowerApplied10_bound : highNormUpper LowerApplied10 ≤ 5844630296783630 :=
  highNormUpper_le_of_rows LowerApplied10 LowerApplied10Rows 5844630296783630 LowerApplied10_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
