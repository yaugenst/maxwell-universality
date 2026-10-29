import Maxwell.Certificate.AppliedWitness.LowerApplied8
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied08Rows : Fin 20 → ℤ := ![40477413375835, 226239191766891, 256949783344783, 300798094544046, 355635782950083, 81621298940469, 429618080881285, 432699421270167, 426462344252646, 412632548612575, 85309183057907, 443243516653014, 437055174745994, 422161025687504, 399469515121985, 72650285783141, 305847294351976, 253608563119172, 216179731858661, 195176573039909]
theorem LowerApplied08X0 : highNormUpperX LowerApplied8 0 = LowerApplied08Rows 0 := by decide +kernel
theorem LowerApplied08X1 : highNormUpperX LowerApplied8 1 = LowerApplied08Rows 1 := by decide +kernel
theorem LowerApplied08X2 : highNormUpperX LowerApplied8 2 = LowerApplied08Rows 2 := by decide +kernel
theorem LowerApplied08X3 : highNormUpperX LowerApplied8 3 = LowerApplied08Rows 3 := by decide +kernel
theorem LowerApplied08X4 : highNormUpperX LowerApplied8 4 = LowerApplied08Rows 4 := by decide +kernel
theorem LowerApplied08X5 : highNormUpperX LowerApplied8 5 = LowerApplied08Rows 5 := by decide +kernel
theorem LowerApplied08X6 : highNormUpperX LowerApplied8 6 = LowerApplied08Rows 6 := by decide +kernel
theorem LowerApplied08X7 : highNormUpperX LowerApplied8 7 = LowerApplied08Rows 7 := by decide +kernel
theorem LowerApplied08X8 : highNormUpperX LowerApplied8 8 = LowerApplied08Rows 8 := by decide +kernel
theorem LowerApplied08X9 : highNormUpperX LowerApplied8 9 = LowerApplied08Rows 9 := by decide +kernel
theorem LowerApplied08X10 : highNormUpperX LowerApplied8 10 = LowerApplied08Rows 10 := by decide +kernel
theorem LowerApplied08X11 : highNormUpperX LowerApplied8 11 = LowerApplied08Rows 11 := by decide +kernel
theorem LowerApplied08X12 : highNormUpperX LowerApplied8 12 = LowerApplied08Rows 12 := by decide +kernel
theorem LowerApplied08X13 : highNormUpperX LowerApplied8 13 = LowerApplied08Rows 13 := by decide +kernel
theorem LowerApplied08X14 : highNormUpperX LowerApplied8 14 = LowerApplied08Rows 14 := by decide +kernel
theorem LowerApplied08X15 : highNormUpperX LowerApplied8 15 = LowerApplied08Rows 15 := by decide +kernel
theorem LowerApplied08X16 : highNormUpperX LowerApplied8 16 = LowerApplied08Rows 16 := by decide +kernel
theorem LowerApplied08X17 : highNormUpperX LowerApplied8 17 = LowerApplied08Rows 17 := by decide +kernel
theorem LowerApplied08X18 : highNormUpperX LowerApplied8 18 = LowerApplied08Rows 18 := by decide +kernel
theorem LowerApplied08X19 : highNormUpperX LowerApplied8 19 = LowerApplied08Rows 19 := by decide +kernel
theorem LowerApplied08_rows (x : Fin 20) : highNormUpperX LowerApplied8 x = LowerApplied08Rows x := by
  fin_cases x
  · exact LowerApplied08X0
  · exact LowerApplied08X1
  · exact LowerApplied08X2
  · exact LowerApplied08X3
  · exact LowerApplied08X4
  · exact LowerApplied08X5
  · exact LowerApplied08X6
  · exact LowerApplied08X7
  · exact LowerApplied08X8
  · exact LowerApplied08X9
  · exact LowerApplied08X10
  · exact LowerApplied08X11
  · exact LowerApplied08X12
  · exact LowerApplied08X13
  · exact LowerApplied08X14
  · exact LowerApplied08X15
  · exact LowerApplied08X16
  · exact LowerApplied08X17
  · exact LowerApplied08X18
  · exact LowerApplied08X19
theorem LowerApplied08_bound : highNormUpper LowerApplied8 ≤ 5793834823358043 :=
  highNormUpper_le_of_rows LowerApplied8 LowerApplied08Rows 5793834823358043 LowerApplied08_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
