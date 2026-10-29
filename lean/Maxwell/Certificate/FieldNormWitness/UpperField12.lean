import Maxwell.Certificate.ProjectionWitness.UpperResult12
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField12Rows : Fin 20 → ℤ := ![15424134141752914871461630457790, 9620739222464696231390958746499, 25885125309981227454047848566979, 1473550414347729847348898336313, 377315934640738451021244948460, 233738903276471168622681308358, 39608136086894810345891510802, 42661711715978317110647899670, 7008588342988187535563996495, 8137563791700718258389252106, 8137563791700731474744904036, 7008588342988007038589195703, 42661711715978758967091946054, 39608136086894341644434516546, 233738903276469674919024065919, 377315934640735568813163637716, 1473550414347716394860947931659, 25885125309981168223292049700928, 9620739222464707924830619779081, 15424134141752980315745194745233]
theorem UpperField12X0 : highNormUpperX UpperResult12 0 = UpperField12Rows 0 := by decide +kernel
theorem UpperField12X1 : highNormUpperX UpperResult12 1 = UpperField12Rows 1 := by decide +kernel
theorem UpperField12X2 : highNormUpperX UpperResult12 2 = UpperField12Rows 2 := by decide +kernel
theorem UpperField12X3 : highNormUpperX UpperResult12 3 = UpperField12Rows 3 := by decide +kernel
theorem UpperField12X4 : highNormUpperX UpperResult12 4 = UpperField12Rows 4 := by decide +kernel
theorem UpperField12X5 : highNormUpperX UpperResult12 5 = UpperField12Rows 5 := by decide +kernel
theorem UpperField12X6 : highNormUpperX UpperResult12 6 = UpperField12Rows 6 := by decide +kernel
theorem UpperField12X7 : highNormUpperX UpperResult12 7 = UpperField12Rows 7 := by decide +kernel
theorem UpperField12X8 : highNormUpperX UpperResult12 8 = UpperField12Rows 8 := by decide +kernel
theorem UpperField12X9 : highNormUpperX UpperResult12 9 = UpperField12Rows 9 := by decide +kernel
theorem UpperField12X10 : highNormUpperX UpperResult12 10 = UpperField12Rows 10 := by decide +kernel
theorem UpperField12X11 : highNormUpperX UpperResult12 11 = UpperField12Rows 11 := by decide +kernel
theorem UpperField12X12 : highNormUpperX UpperResult12 12 = UpperField12Rows 12 := by decide +kernel
theorem UpperField12X13 : highNormUpperX UpperResult12 13 = UpperField12Rows 13 := by decide +kernel
theorem UpperField12X14 : highNormUpperX UpperResult12 14 = UpperField12Rows 14 := by decide +kernel
theorem UpperField12X15 : highNormUpperX UpperResult12 15 = UpperField12Rows 15 := by decide +kernel
theorem UpperField12X16 : highNormUpperX UpperResult12 16 = UpperField12Rows 16 := by decide +kernel
theorem UpperField12X17 : highNormUpperX UpperResult12 17 = UpperField12Rows 17 := by decide +kernel
theorem UpperField12X18 : highNormUpperX UpperResult12 18 = UpperField12Rows 18 := by decide +kernel
theorem UpperField12X19 : highNormUpperX UpperResult12 19 = UpperField12Rows 19 := by decide +kernel
theorem UpperField12_rows (x : Fin 20) : highNormUpperX UpperResult12 x = UpperField12Rows x := by
  fin_cases x
  · exact UpperField12X0
  · exact UpperField12X1
  · exact UpperField12X2
  · exact UpperField12X3
  · exact UpperField12X4
  · exact UpperField12X5
  · exact UpperField12X6
  · exact UpperField12X7
  · exact UpperField12X8
  · exact UpperField12X9
  · exact UpperField12X10
  · exact UpperField12X11
  · exact UpperField12X12
  · exact UpperField12X13
  · exact UpperField12X14
  · exact UpperField12X15
  · exact UpperField12X16
  · exact UpperField12X17
  · exact UpperField12X18
  · exact UpperField12X19
theorem UpperField12_bound : highNormUpper UpperResult12 ≤ 106224039852802679998729615446347 :=
  highNormUpper_le_of_rows UpperResult12 UpperField12Rows 106224039852802679998729615446347 UpperField12_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
