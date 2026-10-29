import Maxwell.Certificate.AppliedWitness.LowerApplied5
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied05Rows : Fin 20 → ℤ := ![40585436335099, 226841328108328, 257638812624891, 301601385110501, 356578546890426, 81835181442849, 430759536023211, 433856983605084, 427600594639258, 413727853249191, 85534784135008, 444423504622540, 438224387773051, 423288498669060, 400525306418723, 72841795996234, 306657292445180, 254289466151970, 216756870953040, 195694948596026]
theorem LowerApplied05X0 : highNormUpperX LowerApplied5 0 = LowerApplied05Rows 0 := by decide +kernel
theorem LowerApplied05X1 : highNormUpperX LowerApplied5 1 = LowerApplied05Rows 1 := by decide +kernel
theorem LowerApplied05X2 : highNormUpperX LowerApplied5 2 = LowerApplied05Rows 2 := by decide +kernel
theorem LowerApplied05X3 : highNormUpperX LowerApplied5 3 = LowerApplied05Rows 3 := by decide +kernel
theorem LowerApplied05X4 : highNormUpperX LowerApplied5 4 = LowerApplied05Rows 4 := by decide +kernel
theorem LowerApplied05X5 : highNormUpperX LowerApplied5 5 = LowerApplied05Rows 5 := by decide +kernel
theorem LowerApplied05X6 : highNormUpperX LowerApplied5 6 = LowerApplied05Rows 6 := by decide +kernel
theorem LowerApplied05X7 : highNormUpperX LowerApplied5 7 = LowerApplied05Rows 7 := by decide +kernel
theorem LowerApplied05X8 : highNormUpperX LowerApplied5 8 = LowerApplied05Rows 8 := by decide +kernel
theorem LowerApplied05X9 : highNormUpperX LowerApplied5 9 = LowerApplied05Rows 9 := by decide +kernel
theorem LowerApplied05X10 : highNormUpperX LowerApplied5 10 = LowerApplied05Rows 10 := by decide +kernel
theorem LowerApplied05X11 : highNormUpperX LowerApplied5 11 = LowerApplied05Rows 11 := by decide +kernel
theorem LowerApplied05X12 : highNormUpperX LowerApplied5 12 = LowerApplied05Rows 12 := by decide +kernel
theorem LowerApplied05X13 : highNormUpperX LowerApplied5 13 = LowerApplied05Rows 13 := by decide +kernel
theorem LowerApplied05X14 : highNormUpperX LowerApplied5 14 = LowerApplied05Rows 14 := by decide +kernel
theorem LowerApplied05X15 : highNormUpperX LowerApplied5 15 = LowerApplied05Rows 15 := by decide +kernel
theorem LowerApplied05X16 : highNormUpperX LowerApplied5 16 = LowerApplied05Rows 16 := by decide +kernel
theorem LowerApplied05X17 : highNormUpperX LowerApplied5 17 = LowerApplied05Rows 17 := by decide +kernel
theorem LowerApplied05X18 : highNormUpperX LowerApplied5 18 = LowerApplied05Rows 18 := by decide +kernel
theorem LowerApplied05X19 : highNormUpperX LowerApplied5 19 = LowerApplied05Rows 19 := by decide +kernel
theorem LowerApplied05_rows (x : Fin 20) : highNormUpperX LowerApplied5 x = LowerApplied05Rows x := by
  fin_cases x
  · exact LowerApplied05X0
  · exact LowerApplied05X1
  · exact LowerApplied05X2
  · exact LowerApplied05X3
  · exact LowerApplied05X4
  · exact LowerApplied05X5
  · exact LowerApplied05X6
  · exact LowerApplied05X7
  · exact LowerApplied05X8
  · exact LowerApplied05X9
  · exact LowerApplied05X10
  · exact LowerApplied05X11
  · exact LowerApplied05X12
  · exact LowerApplied05X13
  · exact LowerApplied05X14
  · exact LowerApplied05X15
  · exact LowerApplied05X16
  · exact LowerApplied05X17
  · exact LowerApplied05X18
  · exact LowerApplied05X19
theorem LowerApplied05_bound : highNormUpper LowerApplied5 ≤ 5809262513789670 :=
  highNormUpper_le_of_rows LowerApplied5 LowerApplied05Rows 5809262513789670 LowerApplied05_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
