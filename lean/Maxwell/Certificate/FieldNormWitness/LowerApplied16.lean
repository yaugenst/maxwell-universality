import Maxwell.Certificate.AppliedWitness.LowerApplied16
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied16Rows : Fin 20 → ℤ := ![39462606999549, 220573088505577, 250510298899054, 293249101815604, 346698193028157, 79564595624264, 418795974727154, 421794724591225, 415718038015420, 402248784322849, 83161364189645, 432081252934858, 426041694934288, 411524864250541, 389411507563024, 70823491709456, 298172471620190, 247254647506329, 210767202086114, 190286111691784]
theorem LowerApplied16X0 : highNormUpperX LowerApplied16 0 = LowerApplied16Rows 0 := by decide +kernel
theorem LowerApplied16X1 : highNormUpperX LowerApplied16 1 = LowerApplied16Rows 1 := by decide +kernel
theorem LowerApplied16X2 : highNormUpperX LowerApplied16 2 = LowerApplied16Rows 2 := by decide +kernel
theorem LowerApplied16X3 : highNormUpperX LowerApplied16 3 = LowerApplied16Rows 3 := by decide +kernel
theorem LowerApplied16X4 : highNormUpperX LowerApplied16 4 = LowerApplied16Rows 4 := by decide +kernel
theorem LowerApplied16X5 : highNormUpperX LowerApplied16 5 = LowerApplied16Rows 5 := by decide +kernel
theorem LowerApplied16X6 : highNormUpperX LowerApplied16 6 = LowerApplied16Rows 6 := by decide +kernel
theorem LowerApplied16X7 : highNormUpperX LowerApplied16 7 = LowerApplied16Rows 7 := by decide +kernel
theorem LowerApplied16X8 : highNormUpperX LowerApplied16 8 = LowerApplied16Rows 8 := by decide +kernel
theorem LowerApplied16X9 : highNormUpperX LowerApplied16 9 = LowerApplied16Rows 9 := by decide +kernel
theorem LowerApplied16X10 : highNormUpperX LowerApplied16 10 = LowerApplied16Rows 10 := by decide +kernel
theorem LowerApplied16X11 : highNormUpperX LowerApplied16 11 = LowerApplied16Rows 11 := by decide +kernel
theorem LowerApplied16X12 : highNormUpperX LowerApplied16 12 = LowerApplied16Rows 12 := by decide +kernel
theorem LowerApplied16X13 : highNormUpperX LowerApplied16 13 = LowerApplied16Rows 13 := by decide +kernel
theorem LowerApplied16X14 : highNormUpperX LowerApplied16 14 = LowerApplied16Rows 14 := by decide +kernel
theorem LowerApplied16X15 : highNormUpperX LowerApplied16 15 = LowerApplied16Rows 15 := by decide +kernel
theorem LowerApplied16X16 : highNormUpperX LowerApplied16 16 = LowerApplied16Rows 16 := by decide +kernel
theorem LowerApplied16X17 : highNormUpperX LowerApplied16 17 = LowerApplied16Rows 17 := by decide +kernel
theorem LowerApplied16X18 : highNormUpperX LowerApplied16 18 = LowerApplied16Rows 18 := by decide +kernel
theorem LowerApplied16X19 : highNormUpperX LowerApplied16 19 = LowerApplied16Rows 19 := by decide +kernel
theorem LowerApplied16_rows (x : Fin 20) : highNormUpperX LowerApplied16 x = LowerApplied16Rows x := by
  fin_cases x
  · exact LowerApplied16X0
  · exact LowerApplied16X1
  · exact LowerApplied16X2
  · exact LowerApplied16X3
  · exact LowerApplied16X4
  · exact LowerApplied16X5
  · exact LowerApplied16X6
  · exact LowerApplied16X7
  · exact LowerApplied16X8
  · exact LowerApplied16X9
  · exact LowerApplied16X10
  · exact LowerApplied16X11
  · exact LowerApplied16X12
  · exact LowerApplied16X13
  · exact LowerApplied16X14
  · exact LowerApplied16X15
  · exact LowerApplied16X16
  · exact LowerApplied16X17
  · exact LowerApplied16X18
  · exact LowerApplied16X19
theorem LowerApplied16_bound : highNormUpper LowerApplied16 ≤ 5648140015015082 :=
  highNormUpper_le_of_rows LowerApplied16 LowerApplied16Rows 5648140015015082 LowerApplied16_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
