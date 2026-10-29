import Maxwell.Certificate.AppliedWitness.LowerApplied26
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied26Rows : Fin 20 → ℤ := ![40132395015794, 224293673899430, 254746073677370, 298243964216876, 352651109769074, 80941702797527, 426080289890810, 429146443469527, 422949891806653, 409203082584640, 84599159147523, 439589475147171, 433464898950329, 418686659523100, 396150917701645, 72039664960371, 303247056529980, 251432863258786, 214317513584115, 193508527335331]
theorem LowerApplied26X0 : highNormUpperX LowerApplied26 0 = LowerApplied26Rows 0 := by decide +kernel
theorem LowerApplied26X1 : highNormUpperX LowerApplied26 1 = LowerApplied26Rows 1 := by decide +kernel
theorem LowerApplied26X2 : highNormUpperX LowerApplied26 2 = LowerApplied26Rows 2 := by decide +kernel
theorem LowerApplied26X3 : highNormUpperX LowerApplied26 3 = LowerApplied26Rows 3 := by decide +kernel
theorem LowerApplied26X4 : highNormUpperX LowerApplied26 4 = LowerApplied26Rows 4 := by decide +kernel
theorem LowerApplied26X5 : highNormUpperX LowerApplied26 5 = LowerApplied26Rows 5 := by decide +kernel
theorem LowerApplied26X6 : highNormUpperX LowerApplied26 6 = LowerApplied26Rows 6 := by decide +kernel
theorem LowerApplied26X7 : highNormUpperX LowerApplied26 7 = LowerApplied26Rows 7 := by decide +kernel
theorem LowerApplied26X8 : highNormUpperX LowerApplied26 8 = LowerApplied26Rows 8 := by decide +kernel
theorem LowerApplied26X9 : highNormUpperX LowerApplied26 9 = LowerApplied26Rows 9 := by decide +kernel
theorem LowerApplied26X10 : highNormUpperX LowerApplied26 10 = LowerApplied26Rows 10 := by decide +kernel
theorem LowerApplied26X11 : highNormUpperX LowerApplied26 11 = LowerApplied26Rows 11 := by decide +kernel
theorem LowerApplied26X12 : highNormUpperX LowerApplied26 12 = LowerApplied26Rows 12 := by decide +kernel
theorem LowerApplied26X13 : highNormUpperX LowerApplied26 13 = LowerApplied26Rows 13 := by decide +kernel
theorem LowerApplied26X14 : highNormUpperX LowerApplied26 14 = LowerApplied26Rows 14 := by decide +kernel
theorem LowerApplied26X15 : highNormUpperX LowerApplied26 15 = LowerApplied26Rows 15 := by decide +kernel
theorem LowerApplied26X16 : highNormUpperX LowerApplied26 16 = LowerApplied26Rows 16 := by decide +kernel
theorem LowerApplied26X17 : highNormUpperX LowerApplied26 17 = LowerApplied26Rows 17 := by decide +kernel
theorem LowerApplied26X18 : highNormUpperX LowerApplied26 18 = LowerApplied26Rows 18 := by decide +kernel
theorem LowerApplied26X19 : highNormUpperX LowerApplied26 19 = LowerApplied26Rows 19 := by decide +kernel
theorem LowerApplied26_rows (x : Fin 20) : highNormUpperX LowerApplied26 x = LowerApplied26Rows x := by
  fin_cases x
  · exact LowerApplied26X0
  · exact LowerApplied26X1
  · exact LowerApplied26X2
  · exact LowerApplied26X3
  · exact LowerApplied26X4
  · exact LowerApplied26X5
  · exact LowerApplied26X6
  · exact LowerApplied26X7
  · exact LowerApplied26X8
  · exact LowerApplied26X9
  · exact LowerApplied26X10
  · exact LowerApplied26X11
  · exact LowerApplied26X12
  · exact LowerApplied26X13
  · exact LowerApplied26X14
  · exact LowerApplied26X15
  · exact LowerApplied26X16
  · exact LowerApplied26X17
  · exact LowerApplied26X18
  · exact LowerApplied26X19
theorem LowerApplied26_bound : highNormUpper LowerApplied26 ≤ 5745425363266052 :=
  highNormUpper_le_of_rows LowerApplied26 LowerApplied26Rows 5745425363266052 LowerApplied26_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
