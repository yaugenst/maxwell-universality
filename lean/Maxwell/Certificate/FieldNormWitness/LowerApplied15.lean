import Maxwell.Certificate.AppliedWitness.LowerApplied15
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied15Rows : Fin 20 → ℤ := ![40422570936001, 225946129825107, 256608174476398, 300380165886700, 355117029758877, 81495615320268, 428948728728265, 432020681593164, 425795681811246, 412006104529455, 85177760308892, 442555446637945, 436370593327732, 421503151105869, 398861335348919, 72543193245317, 305422007901011, 253273293349134, 215901556155620, 194914246412331]
theorem LowerApplied15X0 : highNormUpperX LowerApplied15 0 = LowerApplied15Rows 0 := by decide +kernel
theorem LowerApplied15X1 : highNormUpperX LowerApplied15 1 = LowerApplied15Rows 1 := by decide +kernel
theorem LowerApplied15X2 : highNormUpperX LowerApplied15 2 = LowerApplied15Rows 2 := by decide +kernel
theorem LowerApplied15X3 : highNormUpperX LowerApplied15 3 = LowerApplied15Rows 3 := by decide +kernel
theorem LowerApplied15X4 : highNormUpperX LowerApplied15 4 = LowerApplied15Rows 4 := by decide +kernel
theorem LowerApplied15X5 : highNormUpperX LowerApplied15 5 = LowerApplied15Rows 5 := by decide +kernel
theorem LowerApplied15X6 : highNormUpperX LowerApplied15 6 = LowerApplied15Rows 6 := by decide +kernel
theorem LowerApplied15X7 : highNormUpperX LowerApplied15 7 = LowerApplied15Rows 7 := by decide +kernel
theorem LowerApplied15X8 : highNormUpperX LowerApplied15 8 = LowerApplied15Rows 8 := by decide +kernel
theorem LowerApplied15X9 : highNormUpperX LowerApplied15 9 = LowerApplied15Rows 9 := by decide +kernel
theorem LowerApplied15X10 : highNormUpperX LowerApplied15 10 = LowerApplied15Rows 10 := by decide +kernel
theorem LowerApplied15X11 : highNormUpperX LowerApplied15 11 = LowerApplied15Rows 11 := by decide +kernel
theorem LowerApplied15X12 : highNormUpperX LowerApplied15 12 = LowerApplied15Rows 12 := by decide +kernel
theorem LowerApplied15X13 : highNormUpperX LowerApplied15 13 = LowerApplied15Rows 13 := by decide +kernel
theorem LowerApplied15X14 : highNormUpperX LowerApplied15 14 = LowerApplied15Rows 14 := by decide +kernel
theorem LowerApplied15X15 : highNormUpperX LowerApplied15 15 = LowerApplied15Rows 15 := by decide +kernel
theorem LowerApplied15X16 : highNormUpperX LowerApplied15 16 = LowerApplied15Rows 16 := by decide +kernel
theorem LowerApplied15X17 : highNormUpperX LowerApplied15 17 = LowerApplied15Rows 17 := by decide +kernel
theorem LowerApplied15X18 : highNormUpperX LowerApplied15 18 = LowerApplied15Rows 18 := by decide +kernel
theorem LowerApplied15X19 : highNormUpperX LowerApplied15 19 = LowerApplied15Rows 19 := by decide +kernel
theorem LowerApplied15_rows (x : Fin 20) : highNormUpperX LowerApplied15 x = LowerApplied15Rows x := by
  fin_cases x
  · exact LowerApplied15X0
  · exact LowerApplied15X1
  · exact LowerApplied15X2
  · exact LowerApplied15X3
  · exact LowerApplied15X4
  · exact LowerApplied15X5
  · exact LowerApplied15X6
  · exact LowerApplied15X7
  · exact LowerApplied15X8
  · exact LowerApplied15X9
  · exact LowerApplied15X10
  · exact LowerApplied15X11
  · exact LowerApplied15X12
  · exact LowerApplied15X13
  · exact LowerApplied15X14
  · exact LowerApplied15X15
  · exact LowerApplied15X16
  · exact LowerApplied15X17
  · exact LowerApplied15X18
  · exact LowerApplied15X19
theorem LowerApplied15_bound : highNormUpper LowerApplied15 ≤ 5785263466658251 :=
  highNormUpper_le_of_rows LowerApplied15 LowerApplied15Rows 5785263466658251 LowerApplied15_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
