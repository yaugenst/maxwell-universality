import Maxwell.Certificate.ProjectionWitness.LowerResult5
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField05Rows : Fin 20 → ℤ := ![12199407553121623024750171222975, 13022426293513878120603762728618, 36036335620536132267407859098919, 899802570515861074617794720624, 993037013264078753961122454935, 132256452961935095385872381318, 119805045332013749516103220805, 30810387799116554134947428373, 16020875126361167795722550672, 10398795485655120950912857109, 10398795485654901699537490307, 16020875126360555256726578952, 30810387799116623634313025795, 119805045332011943766297583279, 132256452961933796445851345220, 993037013264064023672687356650, 899802570515831524249909472177, 36036335620535488513520497836630, 13022426293513715839278177892853, 12199407553122052647337733673914]
theorem LowerField05X0 : highNormUpperX LowerResult5 0 = LowerField05Rows 0 := by decide +kernel
theorem LowerField05X1 : highNormUpperX LowerResult5 1 = LowerField05Rows 1 := by decide +kernel
theorem LowerField05X2 : highNormUpperX LowerResult5 2 = LowerField05Rows 2 := by decide +kernel
theorem LowerField05X3 : highNormUpperX LowerResult5 3 = LowerField05Rows 3 := by decide +kernel
theorem LowerField05X4 : highNormUpperX LowerResult5 4 = LowerField05Rows 4 := by decide +kernel
theorem LowerField05X5 : highNormUpperX LowerResult5 5 = LowerField05Rows 5 := by decide +kernel
theorem LowerField05X6 : highNormUpperX LowerResult5 6 = LowerField05Rows 6 := by decide +kernel
theorem LowerField05X7 : highNormUpperX LowerResult5 7 = LowerField05Rows 7 := by decide +kernel
theorem LowerField05X8 : highNormUpperX LowerResult5 8 = LowerField05Rows 8 := by decide +kernel
theorem LowerField05X9 : highNormUpperX LowerResult5 9 = LowerField05Rows 9 := by decide +kernel
theorem LowerField05X10 : highNormUpperX LowerResult5 10 = LowerField05Rows 10 := by decide +kernel
theorem LowerField05X11 : highNormUpperX LowerResult5 11 = LowerField05Rows 11 := by decide +kernel
theorem LowerField05X12 : highNormUpperX LowerResult5 12 = LowerField05Rows 12 := by decide +kernel
theorem LowerField05X13 : highNormUpperX LowerResult5 13 = LowerField05Rows 13 := by decide +kernel
theorem LowerField05X14 : highNormUpperX LowerResult5 14 = LowerField05Rows 14 := by decide +kernel
theorem LowerField05X15 : highNormUpperX LowerResult5 15 = LowerField05Rows 15 := by decide +kernel
theorem LowerField05X16 : highNormUpperX LowerResult5 16 = LowerField05Rows 16 := by decide +kernel
theorem LowerField05X17 : highNormUpperX LowerResult5 17 = LowerField05Rows 17 := by decide +kernel
theorem LowerField05X18 : highNormUpperX LowerResult5 18 = LowerField05Rows 18 := by decide +kernel
theorem LowerField05X19 : highNormUpperX LowerResult5 19 = LowerField05Rows 19 := by decide +kernel
theorem LowerField05_rows (x : Fin 20) : highNormUpperX LowerResult5 x = LowerField05Rows x := by
  fin_cases x
  · exact LowerField05X0
  · exact LowerField05X1
  · exact LowerField05X2
  · exact LowerField05X3
  · exact LowerField05X4
  · exact LowerField05X5
  · exact LowerField05X6
  · exact LowerField05X7
  · exact LowerField05X8
  · exact LowerField05X9
  · exact LowerField05X10
  · exact LowerField05X11
  · exact LowerField05X12
  · exact LowerField05X13
  · exact LowerField05X14
  · exact LowerField05X15
  · exact LowerField05X16
  · exact LowerField05X17
  · exact LowerField05X18
  · exact LowerField05X19
theorem LowerField05_bound : highNormUpper LowerResult5 ≤ 126920601215312885297986000920125 :=
  highNormUpper_le_of_rows LowerResult5 LowerField05Rows 126920601215312885297986000920125 LowerField05_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
