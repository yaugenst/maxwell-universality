import Maxwell.Certificate.ProjectionWitness.LowerResult12
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField12Rows : Fin 20 → ℤ := ![20298611300114403291062546555668, 10115034393811197353522402568425, 26809949918172503601350501376242, 1745918494993809544910406830902, 398833068891635011343962463689, 267512702089811662930796467544, 41001801870000145477139414538, 48648130357809736611268532230, 7917879284592622585769208266, 9378019961007520249813481134, 9378019961007093580356290799, 7917879284591999510522162407, 48648130357810065268397992087, 41001801869998725146352670459, 267512702089809286524235275859, 398833068891631598345636990851, 1745918494993827108107895319149, 26809949918172561868457158625976, 10115034393811179741975680628546, 20298611300114454278306263583383]
theorem LowerField12X0 : highNormUpperX LowerResult12 0 = LowerField12Rows 0 := by decide +kernel
theorem LowerField12X1 : highNormUpperX LowerResult12 1 = LowerField12Rows 1 := by decide +kernel
theorem LowerField12X2 : highNormUpperX LowerResult12 2 = LowerField12Rows 2 := by decide +kernel
theorem LowerField12X3 : highNormUpperX LowerResult12 3 = LowerField12Rows 3 := by decide +kernel
theorem LowerField12X4 : highNormUpperX LowerResult12 4 = LowerField12Rows 4 := by decide +kernel
theorem LowerField12X5 : highNormUpperX LowerResult12 5 = LowerField12Rows 5 := by decide +kernel
theorem LowerField12X6 : highNormUpperX LowerResult12 6 = LowerField12Rows 6 := by decide +kernel
theorem LowerField12X7 : highNormUpperX LowerResult12 7 = LowerField12Rows 7 := by decide +kernel
theorem LowerField12X8 : highNormUpperX LowerResult12 8 = LowerField12Rows 8 := by decide +kernel
theorem LowerField12X9 : highNormUpperX LowerResult12 9 = LowerField12Rows 9 := by decide +kernel
theorem LowerField12X10 : highNormUpperX LowerResult12 10 = LowerField12Rows 10 := by decide +kernel
theorem LowerField12X11 : highNormUpperX LowerResult12 11 = LowerField12Rows 11 := by decide +kernel
theorem LowerField12X12 : highNormUpperX LowerResult12 12 = LowerField12Rows 12 := by decide +kernel
theorem LowerField12X13 : highNormUpperX LowerResult12 13 = LowerField12Rows 13 := by decide +kernel
theorem LowerField12X14 : highNormUpperX LowerResult12 14 = LowerField12Rows 14 := by decide +kernel
theorem LowerField12X15 : highNormUpperX LowerResult12 15 = LowerField12Rows 15 := by decide +kernel
theorem LowerField12X16 : highNormUpperX LowerResult12 16 = LowerField12Rows 16 := by decide +kernel
theorem LowerField12X17 : highNormUpperX LowerResult12 17 = LowerField12Rows 17 := by decide +kernel
theorem LowerField12X18 : highNormUpperX LowerResult12 18 = LowerField12Rows 18 := by decide +kernel
theorem LowerField12X19 : highNormUpperX LowerResult12 19 = LowerField12Rows 19 := by decide +kernel
theorem LowerField12_rows (x : Fin 20) : highNormUpperX LowerResult12 x = LowerField12Rows x := by
  fin_cases x
  · exact LowerField12X0
  · exact LowerField12X1
  · exact LowerField12X2
  · exact LowerField12X3
  · exact LowerField12X4
  · exact LowerField12X5
  · exact LowerField12X6
  · exact LowerField12X7
  · exact LowerField12X8
  · exact LowerField12X9
  · exact LowerField12X10
  · exact LowerField12X11
  · exact LowerField12X12
  · exact LowerField12X13
  · exact LowerField12X14
  · exact LowerField12X15
  · exact LowerField12X16
  · exact LowerField12X17
  · exact LowerField12X18
  · exact LowerField12X19
theorem LowerField12_bound : highNormUpper LowerResult12 ≤ 119485611419093642255267106438154 :=
  highNormUpper_le_of_rows LowerResult12 LowerField12Rows 119485611419093642255267106438154 LowerField12_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
