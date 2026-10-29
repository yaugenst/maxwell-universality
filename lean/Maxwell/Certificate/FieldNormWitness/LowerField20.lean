import Maxwell.Certificate.ProjectionWitness.LowerResult20
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField20Rows : Fin 20 → ℤ := ![20091031913634535953037444937705, 4917661343690876054221906804185, 24259436031640962981349106293076, 1731374735837263051443925701358, 331054054512132523179607101715, 251110098006515059836025160509, 39743846396522247690364871029, 54291190998333930717691555853, 9459698638629565704518241231, 15395434410159655266464141446, 15395434410159160733517654784, 9459698638629672884888003093, 54291190998333333693575594805, 39743846396521471701868966862, 251110098006512692611383429993, 331054054512128582774149831035, 1731374735837246917701557515849, 24259436031640579733645128771410, 4917661343690823073544433210593, 20091031913634488695887587860939]
theorem LowerField20X0 : highNormUpperX LowerResult20 0 = LowerField20Rows 0 := by decide +kernel
theorem LowerField20X1 : highNormUpperX LowerResult20 1 = LowerField20Rows 1 := by decide +kernel
theorem LowerField20X2 : highNormUpperX LowerResult20 2 = LowerField20Rows 2 := by decide +kernel
theorem LowerField20X3 : highNormUpperX LowerResult20 3 = LowerField20Rows 3 := by decide +kernel
theorem LowerField20X4 : highNormUpperX LowerResult20 4 = LowerField20Rows 4 := by decide +kernel
theorem LowerField20X5 : highNormUpperX LowerResult20 5 = LowerField20Rows 5 := by decide +kernel
theorem LowerField20X6 : highNormUpperX LowerResult20 6 = LowerField20Rows 6 := by decide +kernel
theorem LowerField20X7 : highNormUpperX LowerResult20 7 = LowerField20Rows 7 := by decide +kernel
theorem LowerField20X8 : highNormUpperX LowerResult20 8 = LowerField20Rows 8 := by decide +kernel
theorem LowerField20X9 : highNormUpperX LowerResult20 9 = LowerField20Rows 9 := by decide +kernel
theorem LowerField20X10 : highNormUpperX LowerResult20 10 = LowerField20Rows 10 := by decide +kernel
theorem LowerField20X11 : highNormUpperX LowerResult20 11 = LowerField20Rows 11 := by decide +kernel
theorem LowerField20X12 : highNormUpperX LowerResult20 12 = LowerField20Rows 12 := by decide +kernel
theorem LowerField20X13 : highNormUpperX LowerResult20 13 = LowerField20Rows 13 := by decide +kernel
theorem LowerField20X14 : highNormUpperX LowerResult20 14 = LowerField20Rows 14 := by decide +kernel
theorem LowerField20X15 : highNormUpperX LowerResult20 15 = LowerField20Rows 15 := by decide +kernel
theorem LowerField20X16 : highNormUpperX LowerResult20 16 = LowerField20Rows 16 := by decide +kernel
theorem LowerField20X17 : highNormUpperX LowerResult20 17 = LowerField20Rows 17 := by decide +kernel
theorem LowerField20X18 : highNormUpperX LowerResult20 18 = LowerField20Rows 18 := by decide +kernel
theorem LowerField20X19 : highNormUpperX LowerResult20 19 = LowerField20Rows 19 := by decide +kernel
theorem LowerField20_rows (x : Fin 20) : highNormUpperX LowerResult20 x = LowerField20Rows x := by
  fin_cases x
  · exact LowerField20X0
  · exact LowerField20X1
  · exact LowerField20X2
  · exact LowerField20X3
  · exact LowerField20X4
  · exact LowerField20X5
  · exact LowerField20X6
  · exact LowerField20X7
  · exact LowerField20X8
  · exact LowerField20X9
  · exact LowerField20X10
  · exact LowerField20X11
  · exact LowerField20X12
  · exact LowerField20X13
  · exact LowerField20X14
  · exact LowerField20X15
  · exact LowerField20X16
  · exact LowerField20X17
  · exact LowerField20X18
  · exact LowerField20X19
theorem LowerField20_bound : highNormUpper LowerResult20 ≤ 103401116695531354357625145647470 :=
  highNormUpper_le_of_rows LowerResult20 LowerField20Rows 103401116695531354357625145647470 LowerField20_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
