import Maxwell.Certificate.ProjectionWitness.LowerResult1
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField01Rows : Fin 20 → ℤ := ![3824244978188910104135882594532, 12683227270719155112448141494163, 5755234438996605490026473624923, 1322522659333758180670419075527, 296628689787275350108374870643, 133718993569562587461849822446, 46212337369844254842919471168, 18065517078159717997894560549, 8090714881482381258717542355, 1480350319671700104637327088, 1480350319671785494308949884, 8090714881482082620295653595, 18065517078159851742640466463, 46212337369844044087817101975, 133718993569563402222390512964, 296628689787275260712620724027, 1322522659333742841385111205540, 5755234438996544277432550928966, 12683227270718984581758421390901, 3824244978188861304336587184411]
theorem LowerField01X0 : highNormUpperX LowerResult1 0 = LowerField01Rows 0 := by decide +kernel
theorem LowerField01X1 : highNormUpperX LowerResult1 1 = LowerField01Rows 1 := by decide +kernel
theorem LowerField01X2 : highNormUpperX LowerResult1 2 = LowerField01Rows 2 := by decide +kernel
theorem LowerField01X3 : highNormUpperX LowerResult1 3 = LowerField01Rows 3 := by decide +kernel
theorem LowerField01X4 : highNormUpperX LowerResult1 4 = LowerField01Rows 4 := by decide +kernel
theorem LowerField01X5 : highNormUpperX LowerResult1 5 = LowerField01Rows 5 := by decide +kernel
theorem LowerField01X6 : highNormUpperX LowerResult1 6 = LowerField01Rows 6 := by decide +kernel
theorem LowerField01X7 : highNormUpperX LowerResult1 7 = LowerField01Rows 7 := by decide +kernel
theorem LowerField01X8 : highNormUpperX LowerResult1 8 = LowerField01Rows 8 := by decide +kernel
theorem LowerField01X9 : highNormUpperX LowerResult1 9 = LowerField01Rows 9 := by decide +kernel
theorem LowerField01X10 : highNormUpperX LowerResult1 10 = LowerField01Rows 10 := by decide +kernel
theorem LowerField01X11 : highNormUpperX LowerResult1 11 = LowerField01Rows 11 := by decide +kernel
theorem LowerField01X12 : highNormUpperX LowerResult1 12 = LowerField01Rows 12 := by decide +kernel
theorem LowerField01X13 : highNormUpperX LowerResult1 13 = LowerField01Rows 13 := by decide +kernel
theorem LowerField01X14 : highNormUpperX LowerResult1 14 = LowerField01Rows 14 := by decide +kernel
theorem LowerField01X15 : highNormUpperX LowerResult1 15 = LowerField01Rows 15 := by decide +kernel
theorem LowerField01X16 : highNormUpperX LowerResult1 16 = LowerField01Rows 16 := by decide +kernel
theorem LowerField01X17 : highNormUpperX LowerResult1 17 = LowerField01Rows 17 := by decide +kernel
theorem LowerField01X18 : highNormUpperX LowerResult1 18 = LowerField01Rows 18 := by decide +kernel
theorem LowerField01X19 : highNormUpperX LowerResult1 19 = LowerField01Rows 19 := by decide +kernel
theorem LowerField01_rows (x : Fin 20) : highNormUpperX LowerResult1 x = LowerField01Rows x := by
  fin_cases x
  · exact LowerField01X0
  · exact LowerField01X1
  · exact LowerField01X2
  · exact LowerField01X3
  · exact LowerField01X4
  · exact LowerField01X5
  · exact LowerField01X6
  · exact LowerField01X7
  · exact LowerField01X8
  · exact LowerField01X9
  · exact LowerField01X10
  · exact LowerField01X11
  · exact LowerField01X12
  · exact LowerField01X13
  · exact LowerField01X14
  · exact LowerField01X15
  · exact LowerField01X16
  · exact LowerField01X17
  · exact LowerField01X18
  · exact LowerField01X19
theorem LowerField01_bound : highNormUpper LowerResult1 ≤ 48178851900488554310848054502120 :=
  highNormUpper_le_of_rows LowerResult1 LowerField01Rows 48178851900488554310848054502120 LowerField01_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
