import Maxwell.Certificate.ProjectionWitness.LowerResult3
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField03Rows : Fin 20 → ℤ := ![68434174876737223402381244442346, 160566076198675615811350794230032, 34235544260796845078928774189941, 6029326529872153021534751667992, 3598297747717847283384209729536, 489583326532677182664830944510, 568705003398432819138630430694, 80906121629402277780455688178, 91429130445613175896710434658, 16858513864855570612932545247, 16858513864854982987031529758, 91429130445613018811709179905, 80906121629403120875509350085, 568705003398433847135893646290, 489583326532684993491848643993, 3598297747717861131708934341251, 6029326529872216012954569326969, 34235544260796741821872375899254, 160566076198675336620400402972631, 68434174876737801243714916024544]
theorem LowerField03X0 : highNormUpperX LowerResult3 0 = LowerField03Rows 0 := by decide +kernel
theorem LowerField03X1 : highNormUpperX LowerResult3 1 = LowerField03Rows 1 := by decide +kernel
theorem LowerField03X2 : highNormUpperX LowerResult3 2 = LowerField03Rows 2 := by decide +kernel
theorem LowerField03X3 : highNormUpperX LowerResult3 3 = LowerField03Rows 3 := by decide +kernel
theorem LowerField03X4 : highNormUpperX LowerResult3 4 = LowerField03Rows 4 := by decide +kernel
theorem LowerField03X5 : highNormUpperX LowerResult3 5 = LowerField03Rows 5 := by decide +kernel
theorem LowerField03X6 : highNormUpperX LowerResult3 6 = LowerField03Rows 6 := by decide +kernel
theorem LowerField03X7 : highNormUpperX LowerResult3 7 = LowerField03Rows 7 := by decide +kernel
theorem LowerField03X8 : highNormUpperX LowerResult3 8 = LowerField03Rows 8 := by decide +kernel
theorem LowerField03X9 : highNormUpperX LowerResult3 9 = LowerField03Rows 9 := by decide +kernel
theorem LowerField03X10 : highNormUpperX LowerResult3 10 = LowerField03Rows 10 := by decide +kernel
theorem LowerField03X11 : highNormUpperX LowerResult3 11 = LowerField03Rows 11 := by decide +kernel
theorem LowerField03X12 : highNormUpperX LowerResult3 12 = LowerField03Rows 12 := by decide +kernel
theorem LowerField03X13 : highNormUpperX LowerResult3 13 = LowerField03Rows 13 := by decide +kernel
theorem LowerField03X14 : highNormUpperX LowerResult3 14 = LowerField03Rows 14 := by decide +kernel
theorem LowerField03X15 : highNormUpperX LowerResult3 15 = LowerField03Rows 15 := by decide +kernel
theorem LowerField03X16 : highNormUpperX LowerResult3 16 = LowerField03Rows 16 := by decide +kernel
theorem LowerField03X17 : highNormUpperX LowerResult3 17 = LowerField03Rows 17 := by decide +kernel
theorem LowerField03X18 : highNormUpperX LowerResult3 18 = LowerField03Rows 18 := by decide +kernel
theorem LowerField03X19 : highNormUpperX LowerResult3 19 = LowerField03Rows 19 := by decide +kernel
theorem LowerField03_rows (x : Fin 20) : highNormUpperX LowerResult3 x = LowerField03Rows x := by
  fin_cases x
  · exact LowerField03X0
  · exact LowerField03X1
  · exact LowerField03X2
  · exact LowerField03X3
  · exact LowerField03X4
  · exact LowerField03X5
  · exact LowerField03X6
  · exact LowerField03X7
  · exact LowerField03X8
  · exact LowerField03X9
  · exact LowerField03X10
  · exact LowerField03X11
  · exact LowerField03X12
  · exact LowerField03X13
  · exact LowerField03X14
  · exact LowerField03X15
  · exact LowerField03X16
  · exact LowerField03X17
  · exact LowerField03X18
  · exact LowerField03X19
theorem LowerField03_bound : highNormUpper LowerResult3 ≤ 548221803419341612417626525217814 :=
  highNormUpper_le_of_rows LowerResult3 LowerField03Rows 548221803419341612417626525217814 LowerField03_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
