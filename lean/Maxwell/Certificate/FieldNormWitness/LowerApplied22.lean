import Maxwell.Certificate.AppliedWitness.LowerApplied22
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied22Rows : Fin 20 → ℤ := ![40513222536967, 226447957967552, 257185707113692, 301056744037460, 355901358447539, 81676211987768, 429896842388187, 432984169364989, 426750053011511, 412917955903571, 85367190963908, 443534231287525, 437343997811272, 422446075215501, 399742273320919, 72703730236392, 306101084763299, 253842609720028, 216386499747722, 195347402953743]
theorem LowerApplied22X0 : highNormUpperX LowerApplied22 0 = LowerApplied22Rows 0 := by decide +kernel
theorem LowerApplied22X1 : highNormUpperX LowerApplied22 1 = LowerApplied22Rows 1 := by decide +kernel
theorem LowerApplied22X2 : highNormUpperX LowerApplied22 2 = LowerApplied22Rows 2 := by decide +kernel
theorem LowerApplied22X3 : highNormUpperX LowerApplied22 3 = LowerApplied22Rows 3 := by decide +kernel
theorem LowerApplied22X4 : highNormUpperX LowerApplied22 4 = LowerApplied22Rows 4 := by decide +kernel
theorem LowerApplied22X5 : highNormUpperX LowerApplied22 5 = LowerApplied22Rows 5 := by decide +kernel
theorem LowerApplied22X6 : highNormUpperX LowerApplied22 6 = LowerApplied22Rows 6 := by decide +kernel
theorem LowerApplied22X7 : highNormUpperX LowerApplied22 7 = LowerApplied22Rows 7 := by decide +kernel
theorem LowerApplied22X8 : highNormUpperX LowerApplied22 8 = LowerApplied22Rows 8 := by decide +kernel
theorem LowerApplied22X9 : highNormUpperX LowerApplied22 9 = LowerApplied22Rows 9 := by decide +kernel
theorem LowerApplied22X10 : highNormUpperX LowerApplied22 10 = LowerApplied22Rows 10 := by decide +kernel
theorem LowerApplied22X11 : highNormUpperX LowerApplied22 11 = LowerApplied22Rows 11 := by decide +kernel
theorem LowerApplied22X12 : highNormUpperX LowerApplied22 12 = LowerApplied22Rows 12 := by decide +kernel
theorem LowerApplied22X13 : highNormUpperX LowerApplied22 13 = LowerApplied22Rows 13 := by decide +kernel
theorem LowerApplied22X14 : highNormUpperX LowerApplied22 14 = LowerApplied22Rows 14 := by decide +kernel
theorem LowerApplied22X15 : highNormUpperX LowerApplied22 15 = LowerApplied22Rows 15 := by decide +kernel
theorem LowerApplied22X16 : highNormUpperX LowerApplied22 16 = LowerApplied22Rows 16 := by decide +kernel
theorem LowerApplied22X17 : highNormUpperX LowerApplied22 17 = LowerApplied22Rows 17 := by decide +kernel
theorem LowerApplied22X18 : highNormUpperX LowerApplied22 18 = LowerApplied22Rows 18 := by decide +kernel
theorem LowerApplied22X19 : highNormUpperX LowerApplied22 19 = LowerApplied22Rows 19 := by decide +kernel
theorem LowerApplied22_rows (x : Fin 20) : highNormUpperX LowerApplied22 x = LowerApplied22Rows x := by
  fin_cases x
  · exact LowerApplied22X0
  · exact LowerApplied22X1
  · exact LowerApplied22X2
  · exact LowerApplied22X3
  · exact LowerApplied22X4
  · exact LowerApplied22X5
  · exact LowerApplied22X6
  · exact LowerApplied22X7
  · exact LowerApplied22X8
  · exact LowerApplied22X9
  · exact LowerApplied22X10
  · exact LowerApplied22X11
  · exact LowerApplied22X12
  · exact LowerApplied22X13
  · exact LowerApplied22X14
  · exact LowerApplied22X15
  · exact LowerApplied22X16
  · exact LowerApplied22X17
  · exact LowerApplied22X18
  · exact LowerApplied22X19
theorem LowerApplied22_bound : highNormUpper LowerApplied22 ≤ 5798145318779545 :=
  highNormUpper_le_of_rows LowerApplied22 LowerApplied22Rows 5798145318779545 LowerApplied22_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
