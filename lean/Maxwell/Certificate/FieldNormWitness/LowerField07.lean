import Maxwell.Certificate.ProjectionWitness.LowerResult7
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField07Rows : Fin 20 → ℤ := ![19166429632479031363384099511608, 7830940688919860414093939060682, 14038745677324486700723096328924, 804421908647724967738015090796, 300638586829843775349442205292, 100381195719235330699100790449, 42833583043599915411534543374, 26067854678166883805505448191, 10386586764214517144817829803, 7765192908558344971317563992, 7765192908558686647138238004, 10386586764214432872436677489, 26067854678168193976302782379, 42833583043598603099101967764, 100381195719239047266809914805, 300638586829846311976561766412, 804421908647719322317772584835, 14038745677324898013655171468995, 7830940688920252913730891509318, 19166429632479070369704688747857]
theorem LowerField07X0 : highNormUpperX LowerResult7 0 = LowerField07Rows 0 := by decide +kernel
theorem LowerField07X1 : highNormUpperX LowerResult7 1 = LowerField07Rows 1 := by decide +kernel
theorem LowerField07X2 : highNormUpperX LowerResult7 2 = LowerField07Rows 2 := by decide +kernel
theorem LowerField07X3 : highNormUpperX LowerResult7 3 = LowerField07Rows 3 := by decide +kernel
theorem LowerField07X4 : highNormUpperX LowerResult7 4 = LowerField07Rows 4 := by decide +kernel
theorem LowerField07X5 : highNormUpperX LowerResult7 5 = LowerField07Rows 5 := by decide +kernel
theorem LowerField07X6 : highNormUpperX LowerResult7 6 = LowerField07Rows 6 := by decide +kernel
theorem LowerField07X7 : highNormUpperX LowerResult7 7 = LowerField07Rows 7 := by decide +kernel
theorem LowerField07X8 : highNormUpperX LowerResult7 8 = LowerField07Rows 8 := by decide +kernel
theorem LowerField07X9 : highNormUpperX LowerResult7 9 = LowerField07Rows 9 := by decide +kernel
theorem LowerField07X10 : highNormUpperX LowerResult7 10 = LowerField07Rows 10 := by decide +kernel
theorem LowerField07X11 : highNormUpperX LowerResult7 11 = LowerField07Rows 11 := by decide +kernel
theorem LowerField07X12 : highNormUpperX LowerResult7 12 = LowerField07Rows 12 := by decide +kernel
theorem LowerField07X13 : highNormUpperX LowerResult7 13 = LowerField07Rows 13 := by decide +kernel
theorem LowerField07X14 : highNormUpperX LowerResult7 14 = LowerField07Rows 14 := by decide +kernel
theorem LowerField07X15 : highNormUpperX LowerResult7 15 = LowerField07Rows 15 := by decide +kernel
theorem LowerField07X16 : highNormUpperX LowerResult7 16 = LowerField07Rows 16 := by decide +kernel
theorem LowerField07X17 : highNormUpperX LowerResult7 17 = LowerField07Rows 17 := by decide +kernel
theorem LowerField07X18 : highNormUpperX LowerResult7 18 = LowerField07Rows 18 := by decide +kernel
theorem LowerField07X19 : highNormUpperX LowerResult7 19 = LowerField07Rows 19 := by decide +kernel
theorem LowerField07_rows (x : Fin 20) : highNormUpperX LowerResult7 x = LowerField07Rows x := by
  fin_cases x
  · exact LowerField07X0
  · exact LowerField07X1
  · exact LowerField07X2
  · exact LowerField07X3
  · exact LowerField07X4
  · exact LowerField07X5
  · exact LowerField07X6
  · exact LowerField07X7
  · exact LowerField07X8
  · exact LowerField07X9
  · exact LowerField07X10
  · exact LowerField07X11
  · exact LowerField07X12
  · exact LowerField07X13
  · exact LowerField07X14
  · exact LowerField07X15
  · exact LowerField07X16
  · exact LowerField07X17
  · exact LowerField07X18
  · exact LowerField07X19
theorem LowerField07_bound : highNormUpper LowerResult7 ≤ 84657221814630288108567744030969 :=
  highNormUpper_le_of_rows LowerResult7 LowerField07Rows 84657221814630288108567744030969 LowerField07_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
