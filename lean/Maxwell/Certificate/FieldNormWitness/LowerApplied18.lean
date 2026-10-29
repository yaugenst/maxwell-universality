import Maxwell.Certificate.AppliedWitness.LowerApplied18
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied18Rows : Fin 20 → ℤ := ![39951358667774, 223291586008708, 253608440579627, 296898166762020, 351039106185940, 80568333654443, 424103340097550, 427155127062352, 420989137095442, 407318013371706, 84208119598056, 437553313598018, 431454202909012, 416743739073988, 394326592820466, 71709420774355, 301877264965102, 250312427436459, 213367011930567, 192640131688835]
theorem LowerApplied18X0 : highNormUpperX LowerApplied18 0 = LowerApplied18Rows 0 := by decide +kernel
theorem LowerApplied18X1 : highNormUpperX LowerApplied18 1 = LowerApplied18Rows 1 := by decide +kernel
theorem LowerApplied18X2 : highNormUpperX LowerApplied18 2 = LowerApplied18Rows 2 := by decide +kernel
theorem LowerApplied18X3 : highNormUpperX LowerApplied18 3 = LowerApplied18Rows 3 := by decide +kernel
theorem LowerApplied18X4 : highNormUpperX LowerApplied18 4 = LowerApplied18Rows 4 := by decide +kernel
theorem LowerApplied18X5 : highNormUpperX LowerApplied18 5 = LowerApplied18Rows 5 := by decide +kernel
theorem LowerApplied18X6 : highNormUpperX LowerApplied18 6 = LowerApplied18Rows 6 := by decide +kernel
theorem LowerApplied18X7 : highNormUpperX LowerApplied18 7 = LowerApplied18Rows 7 := by decide +kernel
theorem LowerApplied18X8 : highNormUpperX LowerApplied18 8 = LowerApplied18Rows 8 := by decide +kernel
theorem LowerApplied18X9 : highNormUpperX LowerApplied18 9 = LowerApplied18Rows 9 := by decide +kernel
theorem LowerApplied18X10 : highNormUpperX LowerApplied18 10 = LowerApplied18Rows 10 := by decide +kernel
theorem LowerApplied18X11 : highNormUpperX LowerApplied18 11 = LowerApplied18Rows 11 := by decide +kernel
theorem LowerApplied18X12 : highNormUpperX LowerApplied18 12 = LowerApplied18Rows 12 := by decide +kernel
theorem LowerApplied18X13 : highNormUpperX LowerApplied18 13 = LowerApplied18Rows 13 := by decide +kernel
theorem LowerApplied18X14 : highNormUpperX LowerApplied18 14 = LowerApplied18Rows 14 := by decide +kernel
theorem LowerApplied18X15 : highNormUpperX LowerApplied18 15 = LowerApplied18Rows 15 := by decide +kernel
theorem LowerApplied18X16 : highNormUpperX LowerApplied18 16 = LowerApplied18Rows 16 := by decide +kernel
theorem LowerApplied18X17 : highNormUpperX LowerApplied18 17 = LowerApplied18Rows 17 := by decide +kernel
theorem LowerApplied18X18 : highNormUpperX LowerApplied18 18 = LowerApplied18Rows 18 := by decide +kernel
theorem LowerApplied18X19 : highNormUpperX LowerApplied18 19 = LowerApplied18Rows 19 := by decide +kernel
theorem LowerApplied18_rows (x : Fin 20) : highNormUpperX LowerApplied18 x = LowerApplied18Rows x := by
  fin_cases x
  · exact LowerApplied18X0
  · exact LowerApplied18X1
  · exact LowerApplied18X2
  · exact LowerApplied18X3
  · exact LowerApplied18X4
  · exact LowerApplied18X5
  · exact LowerApplied18X6
  · exact LowerApplied18X7
  · exact LowerApplied18X8
  · exact LowerApplied18X9
  · exact LowerApplied18X10
  · exact LowerApplied18X11
  · exact LowerApplied18X12
  · exact LowerApplied18X13
  · exact LowerApplied18X14
  · exact LowerApplied18X15
  · exact LowerApplied18X16
  · exact LowerApplied18X17
  · exact LowerApplied18X18
  · exact LowerApplied18X19
theorem LowerApplied18_bound : highNormUpper LowerApplied18 ≤ 5719114834280420 :=
  highNormUpper_le_of_rows LowerApplied18 LowerApplied18Rows 5719114834280420 LowerApplied18_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
