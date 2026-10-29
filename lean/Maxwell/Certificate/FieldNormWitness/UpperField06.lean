import Maxwell.Certificate.ProjectionWitness.UpperResult6
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField06Rows : Fin 20 → ℤ := ![35068061452066479637928100075926, 24164326823719747577974100396696, 2079972979560976324031687586504, 459319215788022480447786855107, 156778775995911174521820690899, 58466693318928644271805331879, 20597963754540537519624694362, 20200590115543744936301677445, 9855644859261730579547819181, 2880924480095838224154152954, 2880924480095925290532203016, 9855644859261965496755560649, 20200590115543948405310590260, 20597963754540396972738972290, 58466693318928527840570418473, 156778775995911163849761823722, 459319215788035287125424859211, 2079972979560928401504826587385, 24164326823719607720450436300484, 35068061452066501362673621829641]
theorem UpperField06X0 : highNormUpperX UpperResult6 0 = UpperField06Rows 0 := by decide +kernel
theorem UpperField06X1 : highNormUpperX UpperResult6 1 = UpperField06Rows 1 := by decide +kernel
theorem UpperField06X2 : highNormUpperX UpperResult6 2 = UpperField06Rows 2 := by decide +kernel
theorem UpperField06X3 : highNormUpperX UpperResult6 3 = UpperField06Rows 3 := by decide +kernel
theorem UpperField06X4 : highNormUpperX UpperResult6 4 = UpperField06Rows 4 := by decide +kernel
theorem UpperField06X5 : highNormUpperX UpperResult6 5 = UpperField06Rows 5 := by decide +kernel
theorem UpperField06X6 : highNormUpperX UpperResult6 6 = UpperField06Rows 6 := by decide +kernel
theorem UpperField06X7 : highNormUpperX UpperResult6 7 = UpperField06Rows 7 := by decide +kernel
theorem UpperField06X8 : highNormUpperX UpperResult6 8 = UpperField06Rows 8 := by decide +kernel
theorem UpperField06X9 : highNormUpperX UpperResult6 9 = UpperField06Rows 9 := by decide +kernel
theorem UpperField06X10 : highNormUpperX UpperResult6 10 = UpperField06Rows 10 := by decide +kernel
theorem UpperField06X11 : highNormUpperX UpperResult6 11 = UpperField06Rows 11 := by decide +kernel
theorem UpperField06X12 : highNormUpperX UpperResult6 12 = UpperField06Rows 12 := by decide +kernel
theorem UpperField06X13 : highNormUpperX UpperResult6 13 = UpperField06Rows 13 := by decide +kernel
theorem UpperField06X14 : highNormUpperX UpperResult6 14 = UpperField06Rows 14 := by decide +kernel
theorem UpperField06X15 : highNormUpperX UpperResult6 15 = UpperField06Rows 15 := by decide +kernel
theorem UpperField06X16 : highNormUpperX UpperResult6 16 = UpperField06Rows 16 := by decide +kernel
theorem UpperField06X17 : highNormUpperX UpperResult6 17 = UpperField06Rows 17 := by decide +kernel
theorem UpperField06X18 : highNormUpperX UpperResult6 18 = UpperField06Rows 18 := by decide +kernel
theorem UpperField06X19 : highNormUpperX UpperResult6 19 = UpperField06Rows 19 := by decide +kernel
theorem UpperField06_rows (x : Fin 20) : highNormUpperX UpperResult6 x = UpperField06Rows x := by
  fin_cases x
  · exact UpperField06X0
  · exact UpperField06X1
  · exact UpperField06X2
  · exact UpperField06X3
  · exact UpperField06X4
  · exact UpperField06X5
  · exact UpperField06X6
  · exact UpperField06X7
  · exact UpperField06X8
  · exact UpperField06X9
  · exact UpperField06X10
  · exact UpperField06X11
  · exact UpperField06X12
  · exact UpperField06X13
  · exact UpperField06X14
  · exact UpperField06X15
  · exact UpperField06X16
  · exact UpperField06X17
  · exact UpperField06X18
  · exact UpperField06X19
theorem UpperField06_bound : highNormUpper UpperResult6 ≤ 124080922127318862390044908426084 :=
  highNormUpper_le_of_rows UpperResult6 UpperField06Rows 124080922127318862390044908426084 UpperField06_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
