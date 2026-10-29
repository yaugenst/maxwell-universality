import Maxwell.Certificate.AppliedWitness.LowerApplied12
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied12Rows : Fin 20 → ℤ := ![40391464339020, 225758839049541, 256407746699933, 300157315042858, 354863180942912, 81440116802602, 428672356871413, 431756464580037, 425534671736060, 411728359438539, 85120700066858, 442270053366595, 436103349587366, 421244165233064, 398590354358416, 72492162667796, 305185466812320, 253075487734181, 215727860939577, 194762241904473]
theorem LowerApplied12X0 : highNormUpperX LowerApplied12 0 = LowerApplied12Rows 0 := by decide +kernel
theorem LowerApplied12X1 : highNormUpperX LowerApplied12 1 = LowerApplied12Rows 1 := by decide +kernel
theorem LowerApplied12X2 : highNormUpperX LowerApplied12 2 = LowerApplied12Rows 2 := by decide +kernel
theorem LowerApplied12X3 : highNormUpperX LowerApplied12 3 = LowerApplied12Rows 3 := by decide +kernel
theorem LowerApplied12X4 : highNormUpperX LowerApplied12 4 = LowerApplied12Rows 4 := by decide +kernel
theorem LowerApplied12X5 : highNormUpperX LowerApplied12 5 = LowerApplied12Rows 5 := by decide +kernel
theorem LowerApplied12X6 : highNormUpperX LowerApplied12 6 = LowerApplied12Rows 6 := by decide +kernel
theorem LowerApplied12X7 : highNormUpperX LowerApplied12 7 = LowerApplied12Rows 7 := by decide +kernel
theorem LowerApplied12X8 : highNormUpperX LowerApplied12 8 = LowerApplied12Rows 8 := by decide +kernel
theorem LowerApplied12X9 : highNormUpperX LowerApplied12 9 = LowerApplied12Rows 9 := by decide +kernel
theorem LowerApplied12X10 : highNormUpperX LowerApplied12 10 = LowerApplied12Rows 10 := by decide +kernel
theorem LowerApplied12X11 : highNormUpperX LowerApplied12 11 = LowerApplied12Rows 11 := by decide +kernel
theorem LowerApplied12X12 : highNormUpperX LowerApplied12 12 = LowerApplied12Rows 12 := by decide +kernel
theorem LowerApplied12X13 : highNormUpperX LowerApplied12 13 = LowerApplied12Rows 13 := by decide +kernel
theorem LowerApplied12X14 : highNormUpperX LowerApplied12 14 = LowerApplied12Rows 14 := by decide +kernel
theorem LowerApplied12X15 : highNormUpperX LowerApplied12 15 = LowerApplied12Rows 15 := by decide +kernel
theorem LowerApplied12X16 : highNormUpperX LowerApplied12 16 = LowerApplied12Rows 16 := by decide +kernel
theorem LowerApplied12X17 : highNormUpperX LowerApplied12 17 = LowerApplied12Rows 17 := by decide +kernel
theorem LowerApplied12X18 : highNormUpperX LowerApplied12 18 = LowerApplied12Rows 18 := by decide +kernel
theorem LowerApplied12X19 : highNormUpperX LowerApplied12 19 = LowerApplied12Rows 19 := by decide +kernel
theorem LowerApplied12_rows (x : Fin 20) : highNormUpperX LowerApplied12 x = LowerApplied12Rows x := by
  fin_cases x
  · exact LowerApplied12X0
  · exact LowerApplied12X1
  · exact LowerApplied12X2
  · exact LowerApplied12X3
  · exact LowerApplied12X4
  · exact LowerApplied12X5
  · exact LowerApplied12X6
  · exact LowerApplied12X7
  · exact LowerApplied12X8
  · exact LowerApplied12X9
  · exact LowerApplied12X10
  · exact LowerApplied12X11
  · exact LowerApplied12X12
  · exact LowerApplied12X13
  · exact LowerApplied12X14
  · exact LowerApplied12X15
  · exact LowerApplied12X16
  · exact LowerApplied12X17
  · exact LowerApplied12X18
  · exact LowerApplied12X19
theorem LowerApplied12_bound : highNormUpper LowerApplied12 ≤ 5781282358173561 :=
  highNormUpper_le_of_rows LowerApplied12 LowerApplied12Rows 5781282358173561 LowerApplied12_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
