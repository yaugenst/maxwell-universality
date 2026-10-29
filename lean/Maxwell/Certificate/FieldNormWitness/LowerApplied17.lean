import Maxwell.Certificate.AppliedWitness.LowerApplied17
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied17Rows : Fin 20 → ℤ := ![40095244650728, 224119792107124, 254529664779595, 297930221334511, 352205756150249, 80821080619866, 425391049631884, 428422593762969, 422257646496384, 408605335450728, 84475240560121, 438886136846579, 432737346351120, 418001429883666, 395563607566638, 71948542057770, 302934762779361, 251221711927504, 214152004671499, 193334083174557]
theorem LowerApplied17X0 : highNormUpperX LowerApplied17 0 = LowerApplied17Rows 0 := by decide +kernel
theorem LowerApplied17X1 : highNormUpperX LowerApplied17 1 = LowerApplied17Rows 1 := by decide +kernel
theorem LowerApplied17X2 : highNormUpperX LowerApplied17 2 = LowerApplied17Rows 2 := by decide +kernel
theorem LowerApplied17X3 : highNormUpperX LowerApplied17 3 = LowerApplied17Rows 3 := by decide +kernel
theorem LowerApplied17X4 : highNormUpperX LowerApplied17 4 = LowerApplied17Rows 4 := by decide +kernel
theorem LowerApplied17X5 : highNormUpperX LowerApplied17 5 = LowerApplied17Rows 5 := by decide +kernel
theorem LowerApplied17X6 : highNormUpperX LowerApplied17 6 = LowerApplied17Rows 6 := by decide +kernel
theorem LowerApplied17X7 : highNormUpperX LowerApplied17 7 = LowerApplied17Rows 7 := by decide +kernel
theorem LowerApplied17X8 : highNormUpperX LowerApplied17 8 = LowerApplied17Rows 8 := by decide +kernel
theorem LowerApplied17X9 : highNormUpperX LowerApplied17 9 = LowerApplied17Rows 9 := by decide +kernel
theorem LowerApplied17X10 : highNormUpperX LowerApplied17 10 = LowerApplied17Rows 10 := by decide +kernel
theorem LowerApplied17X11 : highNormUpperX LowerApplied17 11 = LowerApplied17Rows 11 := by decide +kernel
theorem LowerApplied17X12 : highNormUpperX LowerApplied17 12 = LowerApplied17Rows 12 := by decide +kernel
theorem LowerApplied17X13 : highNormUpperX LowerApplied17 13 = LowerApplied17Rows 13 := by decide +kernel
theorem LowerApplied17X14 : highNormUpperX LowerApplied17 14 = LowerApplied17Rows 14 := by decide +kernel
theorem LowerApplied17X15 : highNormUpperX LowerApplied17 15 = LowerApplied17Rows 15 := by decide +kernel
theorem LowerApplied17X16 : highNormUpperX LowerApplied17 16 = LowerApplied17Rows 16 := by decide +kernel
theorem LowerApplied17X17 : highNormUpperX LowerApplied17 17 = LowerApplied17Rows 17 := by decide +kernel
theorem LowerApplied17X18 : highNormUpperX LowerApplied17 18 = LowerApplied17Rows 18 := by decide +kernel
theorem LowerApplied17X19 : highNormUpperX LowerApplied17 19 = LowerApplied17Rows 19 := by decide +kernel
theorem LowerApplied17_rows (x : Fin 20) : highNormUpperX LowerApplied17 x = LowerApplied17Rows x := by
  fin_cases x
  · exact LowerApplied17X0
  · exact LowerApplied17X1
  · exact LowerApplied17X2
  · exact LowerApplied17X3
  · exact LowerApplied17X4
  · exact LowerApplied17X5
  · exact LowerApplied17X6
  · exact LowerApplied17X7
  · exact LowerApplied17X8
  · exact LowerApplied17X9
  · exact LowerApplied17X10
  · exact LowerApplied17X11
  · exact LowerApplied17X12
  · exact LowerApplied17X13
  · exact LowerApplied17X14
  · exact LowerApplied17X15
  · exact LowerApplied17X16
  · exact LowerApplied17X17
  · exact LowerApplied17X18
  · exact LowerApplied17X19
theorem LowerApplied17_bound : highNormUpper LowerApplied17 ≤ 5737633250802853 :=
  highNormUpper_le_of_rows LowerApplied17 LowerApplied17Rows 5737633250802853 LowerApplied17_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
