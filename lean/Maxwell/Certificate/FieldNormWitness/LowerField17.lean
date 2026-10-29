import Maxwell.Certificate.ProjectionWitness.LowerResult17
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField17Rows : Fin 20 → ℤ := ![18365969961472591427072924563926, 20377955368587345101925545551242, 11147008457165735192071270051368, 736239775576311699418593971105, 240403671802111100673709803729, 87324907559783759834959071170, 40013561817746800754828638800, 22762770007030776595542237051, 15455108687896613700212438150, 5209975903590844871597268320, 5209975903590629172612129306, 15455108687896666556899557005, 22762770007030919049495336046, 40013561817746823531876882055, 87324907559783005834013380756, 240403671802108881886607707552, 736239775576309407039989533429, 11147008457165592110636879936740, 20377955368587142483654704651604, 18365969961472601614459459038281]
theorem LowerField17X0 : highNormUpperX LowerResult17 0 = LowerField17Rows 0 := by decide +kernel
theorem LowerField17X1 : highNormUpperX LowerResult17 1 = LowerField17Rows 1 := by decide +kernel
theorem LowerField17X2 : highNormUpperX LowerResult17 2 = LowerField17Rows 2 := by decide +kernel
theorem LowerField17X3 : highNormUpperX LowerResult17 3 = LowerField17Rows 3 := by decide +kernel
theorem LowerField17X4 : highNormUpperX LowerResult17 4 = LowerField17Rows 4 := by decide +kernel
theorem LowerField17X5 : highNormUpperX LowerResult17 5 = LowerField17Rows 5 := by decide +kernel
theorem LowerField17X6 : highNormUpperX LowerResult17 6 = LowerField17Rows 6 := by decide +kernel
theorem LowerField17X7 : highNormUpperX LowerResult17 7 = LowerField17Rows 7 := by decide +kernel
theorem LowerField17X8 : highNormUpperX LowerResult17 8 = LowerField17Rows 8 := by decide +kernel
theorem LowerField17X9 : highNormUpperX LowerResult17 9 = LowerField17Rows 9 := by decide +kernel
theorem LowerField17X10 : highNormUpperX LowerResult17 10 = LowerField17Rows 10 := by decide +kernel
theorem LowerField17X11 : highNormUpperX LowerResult17 11 = LowerField17Rows 11 := by decide +kernel
theorem LowerField17X12 : highNormUpperX LowerResult17 12 = LowerField17Rows 12 := by decide +kernel
theorem LowerField17X13 : highNormUpperX LowerResult17 13 = LowerField17Rows 13 := by decide +kernel
theorem LowerField17X14 : highNormUpperX LowerResult17 14 = LowerField17Rows 14 := by decide +kernel
theorem LowerField17X15 : highNormUpperX LowerResult17 15 = LowerField17Rows 15 := by decide +kernel
theorem LowerField17X16 : highNormUpperX LowerResult17 16 = LowerField17Rows 16 := by decide +kernel
theorem LowerField17X17 : highNormUpperX LowerResult17 17 = LowerField17Rows 17 := by decide +kernel
theorem LowerField17X18 : highNormUpperX LowerResult17 18 = LowerField17Rows 18 := by decide +kernel
theorem LowerField17X19 : highNormUpperX LowerResult17 19 = LowerField17Rows 19 := by decide +kernel
theorem LowerField17_rows (x : Fin 20) : highNormUpperX LowerResult17 x = LowerField17Rows x := by
  fin_cases x
  · exact LowerField17X0
  · exact LowerField17X1
  · exact LowerField17X2
  · exact LowerField17X3
  · exact LowerField17X4
  · exact LowerField17X5
  · exact LowerField17X6
  · exact LowerField17X7
  · exact LowerField17X8
  · exact LowerField17X9
  · exact LowerField17X10
  · exact LowerField17X11
  · exact LowerField17X12
  · exact LowerField17X13
  · exact LowerField17X14
  · exact LowerField17X15
  · exact LowerField17X16
  · exact LowerField17X17
  · exact LowerField17X18
  · exact LowerField17X19
theorem LowerField17_bound : highNormUpper LowerResult17 ≤ 102076687117159945858741721747635 :=
  highNormUpper_le_of_rows LowerResult17 LowerField17Rows 102076687117159945858741721747635 LowerField17_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
