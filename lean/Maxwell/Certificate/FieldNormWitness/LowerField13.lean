import Maxwell.Certificate.ProjectionWitness.LowerResult13
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField13Rows : Fin 20 → ℤ := ![8247027081611457571442061172576, 11658218402611432704694913879971, 27283906792937362916450144807577, 790536073418960258617826973008, 483259750656079604484081923679, 114718108621785490358017602297, 54508272259245561950916728294, 24554703786157829710728699768, 6636046330664046851855196638, 6751952364791851750672737889, 6751952364792064327948190948, 6636046330663906621381839609, 24554703786157401615430801287, 54508272259243801607924906870, 114718108621784645869940176589, 483259750656078164613446827405, 790536073418959708094452865057, 27283906792937277310536361778813, 11658218402611456170289161736080, 8247027081611454729656721637145]
theorem LowerField13X0 : highNormUpperX LowerResult13 0 = LowerField13Rows 0 := by decide +kernel
theorem LowerField13X1 : highNormUpperX LowerResult13 1 = LowerField13Rows 1 := by decide +kernel
theorem LowerField13X2 : highNormUpperX LowerResult13 2 = LowerField13Rows 2 := by decide +kernel
theorem LowerField13X3 : highNormUpperX LowerResult13 3 = LowerField13Rows 3 := by decide +kernel
theorem LowerField13X4 : highNormUpperX LowerResult13 4 = LowerField13Rows 4 := by decide +kernel
theorem LowerField13X5 : highNormUpperX LowerResult13 5 = LowerField13Rows 5 := by decide +kernel
theorem LowerField13X6 : highNormUpperX LowerResult13 6 = LowerField13Rows 6 := by decide +kernel
theorem LowerField13X7 : highNormUpperX LowerResult13 7 = LowerField13Rows 7 := by decide +kernel
theorem LowerField13X8 : highNormUpperX LowerResult13 8 = LowerField13Rows 8 := by decide +kernel
theorem LowerField13X9 : highNormUpperX LowerResult13 9 = LowerField13Rows 9 := by decide +kernel
theorem LowerField13X10 : highNormUpperX LowerResult13 10 = LowerField13Rows 10 := by decide +kernel
theorem LowerField13X11 : highNormUpperX LowerResult13 11 = LowerField13Rows 11 := by decide +kernel
theorem LowerField13X12 : highNormUpperX LowerResult13 12 = LowerField13Rows 12 := by decide +kernel
theorem LowerField13X13 : highNormUpperX LowerResult13 13 = LowerField13Rows 13 := by decide +kernel
theorem LowerField13X14 : highNormUpperX LowerResult13 14 = LowerField13Rows 14 := by decide +kernel
theorem LowerField13X15 : highNormUpperX LowerResult13 15 = LowerField13Rows 15 := by decide +kernel
theorem LowerField13X16 : highNormUpperX LowerResult13 16 = LowerField13Rows 16 := by decide +kernel
theorem LowerField13X17 : highNormUpperX LowerResult13 17 = LowerField13Rows 17 := by decide +kernel
theorem LowerField13X18 : highNormUpperX LowerResult13 18 = LowerField13Rows 18 := by decide +kernel
theorem LowerField13X19 : highNormUpperX LowerResult13 19 = LowerField13Rows 19 := by decide +kernel
theorem LowerField13_rows (x : Fin 20) : highNormUpperX LowerResult13 x = LowerField13Rows x := by
  fin_cases x
  · exact LowerField13X0
  · exact LowerField13X1
  · exact LowerField13X2
  · exact LowerField13X3
  · exact LowerField13X4
  · exact LowerField13X5
  · exact LowerField13X6
  · exact LowerField13X7
  · exact LowerField13X8
  · exact LowerField13X9
  · exact LowerField13X10
  · exact LowerField13X11
  · exact LowerField13X12
  · exact LowerField13X13
  · exact LowerField13X14
  · exact LowerField13X15
  · exact LowerField13X16
  · exact LowerField13X17
  · exact LowerField13X18
  · exact LowerField13X19
theorem LowerField13_bound : highNormUpper LowerResult13 ≤ 97340234369195805739543990481500 :=
  highNormUpper_le_of_rows LowerResult13 LowerField13Rows 97340234369195805739543990481500 LowerField13_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
