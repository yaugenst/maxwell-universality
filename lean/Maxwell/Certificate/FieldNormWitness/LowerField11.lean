import Maxwell.Certificate.ProjectionWitness.LowerResult11
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField11Rows : Fin 20 → ℤ := ![26826955151159065902882804009022, 19401972476824650744539921698996, 12010553775548760618572670788181, 930331072130688307790627575280, 315666059497494915527594574670, 150143838631993285600193254254, 50893627754700648216687935626, 31510758808515806742277798527, 17805191828169782971561036174, 6973757362842990220847271600, 6973757362843407318158046252, 17805191828168645522177018739, 31510758808515998643716608014, 50893627754700278508740686187, 150143838631988574604816092651, 315666059497479361447801725977, 930331072130720603011447938097, 12010553775548883855021246853868, 19401972476824754150267549391157, 26826955151158894363770844328063]
theorem LowerField11X0 : highNormUpperX LowerResult11 0 = LowerField11Rows 0 := by decide +kernel
theorem LowerField11X1 : highNormUpperX LowerResult11 1 = LowerField11Rows 1 := by decide +kernel
theorem LowerField11X2 : highNormUpperX LowerResult11 2 = LowerField11Rows 2 := by decide +kernel
theorem LowerField11X3 : highNormUpperX LowerResult11 3 = LowerField11Rows 3 := by decide +kernel
theorem LowerField11X4 : highNormUpperX LowerResult11 4 = LowerField11Rows 4 := by decide +kernel
theorem LowerField11X5 : highNormUpperX LowerResult11 5 = LowerField11Rows 5 := by decide +kernel
theorem LowerField11X6 : highNormUpperX LowerResult11 6 = LowerField11Rows 6 := by decide +kernel
theorem LowerField11X7 : highNormUpperX LowerResult11 7 = LowerField11Rows 7 := by decide +kernel
theorem LowerField11X8 : highNormUpperX LowerResult11 8 = LowerField11Rows 8 := by decide +kernel
theorem LowerField11X9 : highNormUpperX LowerResult11 9 = LowerField11Rows 9 := by decide +kernel
theorem LowerField11X10 : highNormUpperX LowerResult11 10 = LowerField11Rows 10 := by decide +kernel
theorem LowerField11X11 : highNormUpperX LowerResult11 11 = LowerField11Rows 11 := by decide +kernel
theorem LowerField11X12 : highNormUpperX LowerResult11 12 = LowerField11Rows 12 := by decide +kernel
theorem LowerField11X13 : highNormUpperX LowerResult11 13 = LowerField11Rows 13 := by decide +kernel
theorem LowerField11X14 : highNormUpperX LowerResult11 14 = LowerField11Rows 14 := by decide +kernel
theorem LowerField11X15 : highNormUpperX LowerResult11 15 = LowerField11Rows 15 := by decide +kernel
theorem LowerField11X16 : highNormUpperX LowerResult11 16 = LowerField11Rows 16 := by decide +kernel
theorem LowerField11X17 : highNormUpperX LowerResult11 17 = LowerField11Rows 17 := by decide +kernel
theorem LowerField11X18 : highNormUpperX LowerResult11 18 = LowerField11Rows 18 := by decide +kernel
theorem LowerField11X19 : highNormUpperX LowerResult11 19 = LowerField11Rows 19 := by decide +kernel
theorem LowerField11_rows (x : Fin 20) : highNormUpperX LowerResult11 x = LowerField11Rows x := by
  fin_cases x
  · exact LowerField11X0
  · exact LowerField11X1
  · exact LowerField11X2
  · exact LowerField11X3
  · exact LowerField11X4
  · exact LowerField11X5
  · exact LowerField11X6
  · exact LowerField11X7
  · exact LowerField11X8
  · exact LowerField11X9
  · exact LowerField11X10
  · exact LowerField11X11
  · exact LowerField11X12
  · exact LowerField11X13
  · exact LowerField11X14
  · exact LowerField11X15
  · exact LowerField11X16
  · exact LowerField11X17
  · exact LowerField11X18
  · exact LowerField11X19
theorem LowerField11_bound : highNormUpper LowerResult11 ≤ 119485611419093832241181684631335 :=
  highNormUpper_le_of_rows LowerResult11 LowerField11Rows 119485611419093832241181684631335 LowerField11_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
