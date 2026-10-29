import Maxwell.Certificate.AppliedWitness.LowerApplied21
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied21Rows : Fin 20 → ℤ := ![40393171476246, 225774789742532, 256427747249148, 300183242721223, 354896387803728, 81448218423890, 428718778568266, 431807160563460, 425581491130861, 411771436275226, 85128759988704, 442318632898802, 436153357849942, 421289241945822, 398635089257563, 72497158326155, 305211301521933, 253094034151337, 215740190825949, 194772579591313]
theorem LowerApplied21X0 : highNormUpperX LowerApplied21 0 = LowerApplied21Rows 0 := by decide +kernel
theorem LowerApplied21X1 : highNormUpperX LowerApplied21 1 = LowerApplied21Rows 1 := by decide +kernel
theorem LowerApplied21X2 : highNormUpperX LowerApplied21 2 = LowerApplied21Rows 2 := by decide +kernel
theorem LowerApplied21X3 : highNormUpperX LowerApplied21 3 = LowerApplied21Rows 3 := by decide +kernel
theorem LowerApplied21X4 : highNormUpperX LowerApplied21 4 = LowerApplied21Rows 4 := by decide +kernel
theorem LowerApplied21X5 : highNormUpperX LowerApplied21 5 = LowerApplied21Rows 5 := by decide +kernel
theorem LowerApplied21X6 : highNormUpperX LowerApplied21 6 = LowerApplied21Rows 6 := by decide +kernel
theorem LowerApplied21X7 : highNormUpperX LowerApplied21 7 = LowerApplied21Rows 7 := by decide +kernel
theorem LowerApplied21X8 : highNormUpperX LowerApplied21 8 = LowerApplied21Rows 8 := by decide +kernel
theorem LowerApplied21X9 : highNormUpperX LowerApplied21 9 = LowerApplied21Rows 9 := by decide +kernel
theorem LowerApplied21X10 : highNormUpperX LowerApplied21 10 = LowerApplied21Rows 10 := by decide +kernel
theorem LowerApplied21X11 : highNormUpperX LowerApplied21 11 = LowerApplied21Rows 11 := by decide +kernel
theorem LowerApplied21X12 : highNormUpperX LowerApplied21 12 = LowerApplied21Rows 12 := by decide +kernel
theorem LowerApplied21X13 : highNormUpperX LowerApplied21 13 = LowerApplied21Rows 13 := by decide +kernel
theorem LowerApplied21X14 : highNormUpperX LowerApplied21 14 = LowerApplied21Rows 14 := by decide +kernel
theorem LowerApplied21X15 : highNormUpperX LowerApplied21 15 = LowerApplied21Rows 15 := by decide +kernel
theorem LowerApplied21X16 : highNormUpperX LowerApplied21 16 = LowerApplied21Rows 16 := by decide +kernel
theorem LowerApplied21X17 : highNormUpperX LowerApplied21 17 = LowerApplied21Rows 17 := by decide +kernel
theorem LowerApplied21X18 : highNormUpperX LowerApplied21 18 = LowerApplied21Rows 18 := by decide +kernel
theorem LowerApplied21X19 : highNormUpperX LowerApplied21 19 = LowerApplied21Rows 19 := by decide +kernel
theorem LowerApplied21_rows (x : Fin 20) : highNormUpperX LowerApplied21 x = LowerApplied21Rows x := by
  fin_cases x
  · exact LowerApplied21X0
  · exact LowerApplied21X1
  · exact LowerApplied21X2
  · exact LowerApplied21X3
  · exact LowerApplied21X4
  · exact LowerApplied21X5
  · exact LowerApplied21X6
  · exact LowerApplied21X7
  · exact LowerApplied21X8
  · exact LowerApplied21X9
  · exact LowerApplied21X10
  · exact LowerApplied21X11
  · exact LowerApplied21X12
  · exact LowerApplied21X13
  · exact LowerApplied21X14
  · exact LowerApplied21X15
  · exact LowerApplied21X16
  · exact LowerApplied21X17
  · exact LowerApplied21X18
  · exact LowerApplied21X19
theorem LowerApplied21_bound : highNormUpper LowerApplied21 ≤ 5781842770312100 :=
  highNormUpper_le_of_rows LowerApplied21 LowerApplied21Rows 5781842770312100 LowerApplied21_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
