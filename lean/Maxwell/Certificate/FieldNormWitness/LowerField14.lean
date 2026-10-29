import Maxwell.Certificate.ProjectionWitness.LowerResult14
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField14Rows : Fin 20 → ℤ := ![29169595498927017527210401182394, 9693951288556545609091202893359, 9059186063540231843309966791373, 351329736796966241420380009437, 244384879311692996936660437013, 80549890438589764747236958314, 29164115989274446060664467587, 25114341738578289745014171989, 8441963527336524821515567856, 8399405771568922727379767310, 8399405771569299727274379189, 8441963527336484412706537667, 25114341738578614502025285089, 29164115989274416802379087120, 80549890438588757582924734042, 244384879311691440947391804958, 351329736796959467488194142174, 9059186063540201215626638652425, 9693951288556628671463251525643, 29169595498927137041156877140430]
theorem LowerField14X0 : highNormUpperX LowerResult14 0 = LowerField14Rows 0 := by decide +kernel
theorem LowerField14X1 : highNormUpperX LowerResult14 1 = LowerField14Rows 1 := by decide +kernel
theorem LowerField14X2 : highNormUpperX LowerResult14 2 = LowerField14Rows 2 := by decide +kernel
theorem LowerField14X3 : highNormUpperX LowerResult14 3 = LowerField14Rows 3 := by decide +kernel
theorem LowerField14X4 : highNormUpperX LowerResult14 4 = LowerField14Rows 4 := by decide +kernel
theorem LowerField14X5 : highNormUpperX LowerResult14 5 = LowerField14Rows 5 := by decide +kernel
theorem LowerField14X6 : highNormUpperX LowerResult14 6 = LowerField14Rows 6 := by decide +kernel
theorem LowerField14X7 : highNormUpperX LowerResult14 7 = LowerField14Rows 7 := by decide +kernel
theorem LowerField14X8 : highNormUpperX LowerResult14 8 = LowerField14Rows 8 := by decide +kernel
theorem LowerField14X9 : highNormUpperX LowerResult14 9 = LowerField14Rows 9 := by decide +kernel
theorem LowerField14X10 : highNormUpperX LowerResult14 10 = LowerField14Rows 10 := by decide +kernel
theorem LowerField14X11 : highNormUpperX LowerResult14 11 = LowerField14Rows 11 := by decide +kernel
theorem LowerField14X12 : highNormUpperX LowerResult14 12 = LowerField14Rows 12 := by decide +kernel
theorem LowerField14X13 : highNormUpperX LowerResult14 13 = LowerField14Rows 13 := by decide +kernel
theorem LowerField14X14 : highNormUpperX LowerResult14 14 = LowerField14Rows 14 := by decide +kernel
theorem LowerField14X15 : highNormUpperX LowerResult14 15 = LowerField14Rows 15 := by decide +kernel
theorem LowerField14X16 : highNormUpperX LowerResult14 16 = LowerField14Rows 16 := by decide +kernel
theorem LowerField14X17 : highNormUpperX LowerResult14 17 = LowerField14Rows 17 := by decide +kernel
theorem LowerField14X18 : highNormUpperX LowerResult14 18 = LowerField14Rows 18 := by decide +kernel
theorem LowerField14X19 : highNormUpperX LowerResult14 19 = LowerField14Rows 19 := by decide +kernel
theorem LowerField14_rows (x : Fin 20) : highNormUpperX LowerResult14 x = LowerField14Rows x := by
  fin_cases x
  · exact LowerField14X0
  · exact LowerField14X1
  · exact LowerField14X2
  · exact LowerField14X3
  · exact LowerField14X4
  · exact LowerField14X5
  · exact LowerField14X6
  · exact LowerField14X7
  · exact LowerField14X8
  · exact LowerField14X9
  · exact LowerField14X10
  · exact LowerField14X11
  · exact LowerField14X12
  · exact LowerField14X13
  · exact LowerField14X14
  · exact LowerField14X15
  · exact LowerField14X16
  · exact LowerField14X17
  · exact LowerField14X18
  · exact LowerField14X19
theorem LowerField14_bound : highNormUpper LowerResult14 ≤ 97340234369195767575780085535369 :=
  highNormUpper_le_of_rows LowerResult14 LowerField14Rows 97340234369195767575780085535369 LowerField14_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
