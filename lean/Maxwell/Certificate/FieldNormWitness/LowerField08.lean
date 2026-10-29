import Maxwell.Certificate.ProjectionWitness.LowerResult8
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField08Rows : Fin 20 → ℤ := ![14779080590470288498089755038277, 8191712094994401225242694032467, 23006289460330187712632882138310, 1400756302208820236758395984890, 430439990371099821603525774685, 187178935092689023999048009204, 55471942249186146541668653916, 34887844107812560132241110209, 12602087264334886076576036660, 8025753668671220468931777543, 8025753668671378183531083600, 12602087264334944868910794163, 34887844107812265816339680260, 55471942249185624089322775621, 187178935092688120202644648916, 430439990371101246818047066743, 1400756302208801131616156184273, 23006289460330105810052131000095, 8191712094994427511076521835498, 14779080590470179214196146530651]
theorem LowerField08X0 : highNormUpperX LowerResult8 0 = LowerField08Rows 0 := by decide +kernel
theorem LowerField08X1 : highNormUpperX LowerResult8 1 = LowerField08Rows 1 := by decide +kernel
theorem LowerField08X2 : highNormUpperX LowerResult8 2 = LowerField08Rows 2 := by decide +kernel
theorem LowerField08X3 : highNormUpperX LowerResult8 3 = LowerField08Rows 3 := by decide +kernel
theorem LowerField08X4 : highNormUpperX LowerResult8 4 = LowerField08Rows 4 := by decide +kernel
theorem LowerField08X5 : highNormUpperX LowerResult8 5 = LowerField08Rows 5 := by decide +kernel
theorem LowerField08X6 : highNormUpperX LowerResult8 6 = LowerField08Rows 6 := by decide +kernel
theorem LowerField08X7 : highNormUpperX LowerResult8 7 = LowerField08Rows 7 := by decide +kernel
theorem LowerField08X8 : highNormUpperX LowerResult8 8 = LowerField08Rows 8 := by decide +kernel
theorem LowerField08X9 : highNormUpperX LowerResult8 9 = LowerField08Rows 9 := by decide +kernel
theorem LowerField08X10 : highNormUpperX LowerResult8 10 = LowerField08Rows 10 := by decide +kernel
theorem LowerField08X11 : highNormUpperX LowerResult8 11 = LowerField08Rows 11 := by decide +kernel
theorem LowerField08X12 : highNormUpperX LowerResult8 12 = LowerField08Rows 12 := by decide +kernel
theorem LowerField08X13 : highNormUpperX LowerResult8 13 = LowerField08Rows 13 := by decide +kernel
theorem LowerField08X14 : highNormUpperX LowerResult8 14 = LowerField08Rows 14 := by decide +kernel
theorem LowerField08X15 : highNormUpperX LowerResult8 15 = LowerField08Rows 15 := by decide +kernel
theorem LowerField08X16 : highNormUpperX LowerResult8 16 = LowerField08Rows 16 := by decide +kernel
theorem LowerField08X17 : highNormUpperX LowerResult8 17 = LowerField08Rows 17 := by decide +kernel
theorem LowerField08X18 : highNormUpperX LowerResult8 18 = LowerField08Rows 18 := by decide +kernel
theorem LowerField08X19 : highNormUpperX LowerResult8 19 = LowerField08Rows 19 := by decide +kernel
theorem LowerField08_rows (x : Fin 20) : highNormUpperX LowerResult8 x = LowerField08Rows x := by
  fin_cases x
  · exact LowerField08X0
  · exact LowerField08X1
  · exact LowerField08X2
  · exact LowerField08X3
  · exact LowerField08X4
  · exact LowerField08X5
  · exact LowerField08X6
  · exact LowerField08X7
  · exact LowerField08X8
  · exact LowerField08X9
  · exact LowerField08X10
  · exact LowerField08X11
  · exact LowerField08X12
  · exact LowerField08X13
  · exact LowerField08X14
  · exact LowerField08X15
  · exact LowerField08X16
  · exact LowerField08X17
  · exact LowerField08X18
  · exact LowerField08X19
theorem LowerField08_bound : highNormUpper LowerResult8 ≤ 96212890001514798578465470155981 :=
  highNormUpper_le_of_rows LowerResult8 LowerField08Rows 96212890001514798578465470155981 LowerField08_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
