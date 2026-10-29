import Maxwell.Certificate.AppliedWitness.LowerApplied25
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied25Rows : Fin 20 → ℤ := ![39828688292904, 222630342816426, 252843759076104, 295972084108397, 349908409070314, 80297289041819, 422657516263960, 425678404476355, 419547305369161, 405963431298442, 83927100547856, 436062689158576, 429964465583127, 415317309213280, 393007580409674, 71477310010282, 300940665368477, 249557730135793, 212732419133360, 192051408357488]
theorem LowerApplied25X0 : highNormUpperX LowerApplied25 0 = LowerApplied25Rows 0 := by decide +kernel
theorem LowerApplied25X1 : highNormUpperX LowerApplied25 1 = LowerApplied25Rows 1 := by decide +kernel
theorem LowerApplied25X2 : highNormUpperX LowerApplied25 2 = LowerApplied25Rows 2 := by decide +kernel
theorem LowerApplied25X3 : highNormUpperX LowerApplied25 3 = LowerApplied25Rows 3 := by decide +kernel
theorem LowerApplied25X4 : highNormUpperX LowerApplied25 4 = LowerApplied25Rows 4 := by decide +kernel
theorem LowerApplied25X5 : highNormUpperX LowerApplied25 5 = LowerApplied25Rows 5 := by decide +kernel
theorem LowerApplied25X6 : highNormUpperX LowerApplied25 6 = LowerApplied25Rows 6 := by decide +kernel
theorem LowerApplied25X7 : highNormUpperX LowerApplied25 7 = LowerApplied25Rows 7 := by decide +kernel
theorem LowerApplied25X8 : highNormUpperX LowerApplied25 8 = LowerApplied25Rows 8 := by decide +kernel
theorem LowerApplied25X9 : highNormUpperX LowerApplied25 9 = LowerApplied25Rows 9 := by decide +kernel
theorem LowerApplied25X10 : highNormUpperX LowerApplied25 10 = LowerApplied25Rows 10 := by decide +kernel
theorem LowerApplied25X11 : highNormUpperX LowerApplied25 11 = LowerApplied25Rows 11 := by decide +kernel
theorem LowerApplied25X12 : highNormUpperX LowerApplied25 12 = LowerApplied25Rows 12 := by decide +kernel
theorem LowerApplied25X13 : highNormUpperX LowerApplied25 13 = LowerApplied25Rows 13 := by decide +kernel
theorem LowerApplied25X14 : highNormUpperX LowerApplied25 14 = LowerApplied25Rows 14 := by decide +kernel
theorem LowerApplied25X15 : highNormUpperX LowerApplied25 15 = LowerApplied25Rows 15 := by decide +kernel
theorem LowerApplied25X16 : highNormUpperX LowerApplied25 16 = LowerApplied25Rows 16 := by decide +kernel
theorem LowerApplied25X17 : highNormUpperX LowerApplied25 17 = LowerApplied25Rows 17 := by decide +kernel
theorem LowerApplied25X18 : highNormUpperX LowerApplied25 18 = LowerApplied25Rows 18 := by decide +kernel
theorem LowerApplied25X19 : highNormUpperX LowerApplied25 19 = LowerApplied25Rows 19 := by decide +kernel
theorem LowerApplied25_rows (x : Fin 20) : highNormUpperX LowerApplied25 x = LowerApplied25Rows x := by
  fin_cases x
  · exact LowerApplied25X0
  · exact LowerApplied25X1
  · exact LowerApplied25X2
  · exact LowerApplied25X3
  · exact LowerApplied25X4
  · exact LowerApplied25X5
  · exact LowerApplied25X6
  · exact LowerApplied25X7
  · exact LowerApplied25X8
  · exact LowerApplied25X9
  · exact LowerApplied25X10
  · exact LowerApplied25X11
  · exact LowerApplied25X12
  · exact LowerApplied25X13
  · exact LowerApplied25X14
  · exact LowerApplied25X15
  · exact LowerApplied25X16
  · exact LowerApplied25X17
  · exact LowerApplied25X18
  · exact LowerApplied25X19
theorem LowerApplied25_bound : highNormUpper LowerApplied25 ≤ 5700365907731795 :=
  highNormUpper_le_of_rows LowerApplied25 LowerApplied25Rows 5700365907731795 LowerApplied25_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
