import Maxwell.Certificate.AppliedWitness.LowerApplied1
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied01Rows : Fin 20 → ℤ := ![40776620634927, 227922004747440, 258854987483884, 303014202670255, 358248207872435, 82212824293013, 432738333847545, 435825814244505, 429546196884413, 415643655435937, 85928091785560, 446466596757001, 440214357230382, 425214759453887, 402382743006332, 73181274100945, 308107783067057, 255491730567770, 217786790762134, 196625897754134]
theorem LowerApplied01X0 : highNormUpperX LowerApplied1 0 = LowerApplied01Rows 0 := by decide +kernel
theorem LowerApplied01X1 : highNormUpperX LowerApplied1 1 = LowerApplied01Rows 1 := by decide +kernel
theorem LowerApplied01X2 : highNormUpperX LowerApplied1 2 = LowerApplied01Rows 2 := by decide +kernel
theorem LowerApplied01X3 : highNormUpperX LowerApplied1 3 = LowerApplied01Rows 3 := by decide +kernel
theorem LowerApplied01X4 : highNormUpperX LowerApplied1 4 = LowerApplied01Rows 4 := by decide +kernel
theorem LowerApplied01X5 : highNormUpperX LowerApplied1 5 = LowerApplied01Rows 5 := by decide +kernel
theorem LowerApplied01X6 : highNormUpperX LowerApplied1 6 = LowerApplied01Rows 6 := by decide +kernel
theorem LowerApplied01X7 : highNormUpperX LowerApplied1 7 = LowerApplied01Rows 7 := by decide +kernel
theorem LowerApplied01X8 : highNormUpperX LowerApplied1 8 = LowerApplied01Rows 8 := by decide +kernel
theorem LowerApplied01X9 : highNormUpperX LowerApplied1 9 = LowerApplied01Rows 9 := by decide +kernel
theorem LowerApplied01X10 : highNormUpperX LowerApplied1 10 = LowerApplied01Rows 10 := by decide +kernel
theorem LowerApplied01X11 : highNormUpperX LowerApplied1 11 = LowerApplied01Rows 11 := by decide +kernel
theorem LowerApplied01X12 : highNormUpperX LowerApplied1 12 = LowerApplied01Rows 12 := by decide +kernel
theorem LowerApplied01X13 : highNormUpperX LowerApplied1 13 = LowerApplied01Rows 13 := by decide +kernel
theorem LowerApplied01X14 : highNormUpperX LowerApplied1 14 = LowerApplied01Rows 14 := by decide +kernel
theorem LowerApplied01X15 : highNormUpperX LowerApplied1 15 = LowerApplied01Rows 15 := by decide +kernel
theorem LowerApplied01X16 : highNormUpperX LowerApplied1 16 = LowerApplied01Rows 16 := by decide +kernel
theorem LowerApplied01X17 : highNormUpperX LowerApplied1 17 = LowerApplied01Rows 17 := by decide +kernel
theorem LowerApplied01X18 : highNormUpperX LowerApplied1 18 = LowerApplied01Rows 18 := by decide +kernel
theorem LowerApplied01X19 : highNormUpperX LowerApplied1 19 = LowerApplied01Rows 19 := by decide +kernel
theorem LowerApplied01_rows (x : Fin 20) : highNormUpperX LowerApplied1 x = LowerApplied01Rows x := by
  fin_cases x
  · exact LowerApplied01X0
  · exact LowerApplied01X1
  · exact LowerApplied01X2
  · exact LowerApplied01X3
  · exact LowerApplied01X4
  · exact LowerApplied01X5
  · exact LowerApplied01X6
  · exact LowerApplied01X7
  · exact LowerApplied01X8
  · exact LowerApplied01X9
  · exact LowerApplied01X10
  · exact LowerApplied01X11
  · exact LowerApplied01X12
  · exact LowerApplied01X13
  · exact LowerApplied01X14
  · exact LowerApplied01X15
  · exact LowerApplied01X16
  · exact LowerApplied01X17
  · exact LowerApplied01X18
  · exact LowerApplied01X19
theorem LowerApplied01_bound : highNormUpper LowerApplied1 ≤ 5836182872599556 :=
  highNormUpper_le_of_rows LowerApplied1 LowerApplied01Rows 5836182872599556 LowerApplied01_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
