import Maxwell.Certificate.ProjectionWitness.LowerResult21
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField21Rows : Fin 20 → ℤ := ![24835571993874416002142001941678, 10696516464188006357845968392085, 14404064018478928253448669147836, 1261998977585178038613609994848, 280264430978794872506282846194, 136516127395237304310158281226, 37309261059316910498343110958, 30756632270649385444583508872, 7482029432994901992720447376, 10078412502005832928969320786, 10078412502005863284321266825, 7482029432994960714444816789, 30756632270649289717114766339, 37309261059317738421506003585, 136516127395237594410032210120, 280264430978794891780568197162, 1261998977585165079894298998609, 14404064018478811154696046668942, 10696516464187880233454637639537, 24835571993874727944745435275418]
theorem LowerField21X0 : highNormUpperX LowerResult21 0 = LowerField21Rows 0 := by decide +kernel
theorem LowerField21X1 : highNormUpperX LowerResult21 1 = LowerField21Rows 1 := by decide +kernel
theorem LowerField21X2 : highNormUpperX LowerResult21 2 = LowerField21Rows 2 := by decide +kernel
theorem LowerField21X3 : highNormUpperX LowerResult21 3 = LowerField21Rows 3 := by decide +kernel
theorem LowerField21X4 : highNormUpperX LowerResult21 4 = LowerField21Rows 4 := by decide +kernel
theorem LowerField21X5 : highNormUpperX LowerResult21 5 = LowerField21Rows 5 := by decide +kernel
theorem LowerField21X6 : highNormUpperX LowerResult21 6 = LowerField21Rows 6 := by decide +kernel
theorem LowerField21X7 : highNormUpperX LowerResult21 7 = LowerField21Rows 7 := by decide +kernel
theorem LowerField21X8 : highNormUpperX LowerResult21 8 = LowerField21Rows 8 := by decide +kernel
theorem LowerField21X9 : highNormUpperX LowerResult21 9 = LowerField21Rows 9 := by decide +kernel
theorem LowerField21X10 : highNormUpperX LowerResult21 10 = LowerField21Rows 10 := by decide +kernel
theorem LowerField21X11 : highNormUpperX LowerResult21 11 = LowerField21Rows 11 := by decide +kernel
theorem LowerField21X12 : highNormUpperX LowerResult21 12 = LowerField21Rows 12 := by decide +kernel
theorem LowerField21X13 : highNormUpperX LowerResult21 13 = LowerField21Rows 13 := by decide +kernel
theorem LowerField21X14 : highNormUpperX LowerResult21 14 = LowerField21Rows 14 := by decide +kernel
theorem LowerField21X15 : highNormUpperX LowerResult21 15 = LowerField21Rows 15 := by decide +kernel
theorem LowerField21X16 : highNormUpperX LowerResult21 16 = LowerField21Rows 16 := by decide +kernel
theorem LowerField21X17 : highNormUpperX LowerResult21 17 = LowerField21Rows 17 := by decide +kernel
theorem LowerField21X18 : highNormUpperX LowerResult21 18 = LowerField21Rows 18 := by decide +kernel
theorem LowerField21X19 : highNormUpperX LowerResult21 19 = LowerField21Rows 19 := by decide +kernel
theorem LowerField21_rows (x : Fin 20) : highNormUpperX LowerResult21 x = LowerField21Rows x := by
  fin_cases x
  · exact LowerField21X0
  · exact LowerField21X1
  · exact LowerField21X2
  · exact LowerField21X3
  · exact LowerField21X4
  · exact LowerField21X5
  · exact LowerField21X6
  · exact LowerField21X7
  · exact LowerField21X8
  · exact LowerField21X9
  · exact LowerField21X10
  · exact LowerField21X11
  · exact LowerField21X12
  · exact LowerField21X13
  · exact LowerField21X14
  · exact LowerField21X15
  · exact LowerField21X16
  · exact LowerField21X17
  · exact LowerField21X18
  · exact LowerField21X19
theorem LowerField21_bound : highNormUpper LowerResult21 ≤ 103401116695531112610849712835185 :=
  highNormUpper_le_of_rows LowerResult21 LowerField21Rows 103401116695531112610849712835185 LowerField21_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
