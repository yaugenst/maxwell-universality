import Maxwell.Certificate.AppliedWitness.LowerApplied19
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied19Rows : Fin 20 → ℤ := ![38866959997615, 217240096129031, 246719223739720, 288814778794752, 341465040549474, 78363322014632, 412481557924438, 415428221905608, 409439487636073, 396181318675299, 81906247467271, 425563805159939, 419610391851353, 405311382168335, 383537078054891, 69753895639318, 293669404359994, 243512316547736, 207575654904512, 187411057110983]
theorem LowerApplied19X0 : highNormUpperX LowerApplied19 0 = LowerApplied19Rows 0 := by decide +kernel
theorem LowerApplied19X1 : highNormUpperX LowerApplied19 1 = LowerApplied19Rows 1 := by decide +kernel
theorem LowerApplied19X2 : highNormUpperX LowerApplied19 2 = LowerApplied19Rows 2 := by decide +kernel
theorem LowerApplied19X3 : highNormUpperX LowerApplied19 3 = LowerApplied19Rows 3 := by decide +kernel
theorem LowerApplied19X4 : highNormUpperX LowerApplied19 4 = LowerApplied19Rows 4 := by decide +kernel
theorem LowerApplied19X5 : highNormUpperX LowerApplied19 5 = LowerApplied19Rows 5 := by decide +kernel
theorem LowerApplied19X6 : highNormUpperX LowerApplied19 6 = LowerApplied19Rows 6 := by decide +kernel
theorem LowerApplied19X7 : highNormUpperX LowerApplied19 7 = LowerApplied19Rows 7 := by decide +kernel
theorem LowerApplied19X8 : highNormUpperX LowerApplied19 8 = LowerApplied19Rows 8 := by decide +kernel
theorem LowerApplied19X9 : highNormUpperX LowerApplied19 9 = LowerApplied19Rows 9 := by decide +kernel
theorem LowerApplied19X10 : highNormUpperX LowerApplied19 10 = LowerApplied19Rows 10 := by decide +kernel
theorem LowerApplied19X11 : highNormUpperX LowerApplied19 11 = LowerApplied19Rows 11 := by decide +kernel
theorem LowerApplied19X12 : highNormUpperX LowerApplied19 12 = LowerApplied19Rows 12 := by decide +kernel
theorem LowerApplied19X13 : highNormUpperX LowerApplied19 13 = LowerApplied19Rows 13 := by decide +kernel
theorem LowerApplied19X14 : highNormUpperX LowerApplied19 14 = LowerApplied19Rows 14 := by decide +kernel
theorem LowerApplied19X15 : highNormUpperX LowerApplied19 15 = LowerApplied19Rows 15 := by decide +kernel
theorem LowerApplied19X16 : highNormUpperX LowerApplied19 16 = LowerApplied19Rows 16 := by decide +kernel
theorem LowerApplied19X17 : highNormUpperX LowerApplied19 17 = LowerApplied19Rows 17 := by decide +kernel
theorem LowerApplied19X18 : highNormUpperX LowerApplied19 18 = LowerApplied19Rows 18 := by decide +kernel
theorem LowerApplied19X19 : highNormUpperX LowerApplied19 19 = LowerApplied19Rows 19 := by decide +kernel
theorem LowerApplied19_rows (x : Fin 20) : highNormUpperX LowerApplied19 x = LowerApplied19Rows x := by
  fin_cases x
  · exact LowerApplied19X0
  · exact LowerApplied19X1
  · exact LowerApplied19X2
  · exact LowerApplied19X3
  · exact LowerApplied19X4
  · exact LowerApplied19X5
  · exact LowerApplied19X6
  · exact LowerApplied19X7
  · exact LowerApplied19X8
  · exact LowerApplied19X9
  · exact LowerApplied19X10
  · exact LowerApplied19X11
  · exact LowerApplied19X12
  · exact LowerApplied19X13
  · exact LowerApplied19X14
  · exact LowerApplied19X15
  · exact LowerApplied19X16
  · exact LowerApplied19X17
  · exact LowerApplied19X18
  · exact LowerApplied19X19
theorem LowerApplied19_bound : highNormUpper LowerApplied19 ≤ 5562851240630974 :=
  highNormUpper_le_of_rows LowerApplied19 LowerApplied19Rows 5562851240630974 LowerApplied19_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
