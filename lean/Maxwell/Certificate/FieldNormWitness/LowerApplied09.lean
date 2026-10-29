import Maxwell.Certificate.AppliedWitness.LowerApplied9
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied09Rows : Fin 20 → ℤ := ![40679895148967, 227384838136641, 258242863660016, 302284279911230, 357365140910289, 82006683214610, 431646892304284, 434724422368913, 428464389149456, 414601786401398, 85713991522193, 445336880758305, 439102791259514, 424148253358683, 401370182038266, 73001475905269, 307361253958464, 254886888007891, 217273123269263, 196157007860199]
theorem LowerApplied09X0 : highNormUpperX LowerApplied9 0 = LowerApplied09Rows 0 := by decide +kernel
theorem LowerApplied09X1 : highNormUpperX LowerApplied9 1 = LowerApplied09Rows 1 := by decide +kernel
theorem LowerApplied09X2 : highNormUpperX LowerApplied9 2 = LowerApplied09Rows 2 := by decide +kernel
theorem LowerApplied09X3 : highNormUpperX LowerApplied9 3 = LowerApplied09Rows 3 := by decide +kernel
theorem LowerApplied09X4 : highNormUpperX LowerApplied9 4 = LowerApplied09Rows 4 := by decide +kernel
theorem LowerApplied09X5 : highNormUpperX LowerApplied9 5 = LowerApplied09Rows 5 := by decide +kernel
theorem LowerApplied09X6 : highNormUpperX LowerApplied9 6 = LowerApplied09Rows 6 := by decide +kernel
theorem LowerApplied09X7 : highNormUpperX LowerApplied9 7 = LowerApplied09Rows 7 := by decide +kernel
theorem LowerApplied09X8 : highNormUpperX LowerApplied9 8 = LowerApplied09Rows 8 := by decide +kernel
theorem LowerApplied09X9 : highNormUpperX LowerApplied9 9 = LowerApplied09Rows 9 := by decide +kernel
theorem LowerApplied09X10 : highNormUpperX LowerApplied9 10 = LowerApplied09Rows 10 := by decide +kernel
theorem LowerApplied09X11 : highNormUpperX LowerApplied9 11 = LowerApplied09Rows 11 := by decide +kernel
theorem LowerApplied09X12 : highNormUpperX LowerApplied9 12 = LowerApplied09Rows 12 := by decide +kernel
theorem LowerApplied09X13 : highNormUpperX LowerApplied9 13 = LowerApplied09Rows 13 := by decide +kernel
theorem LowerApplied09X14 : highNormUpperX LowerApplied9 14 = LowerApplied09Rows 14 := by decide +kernel
theorem LowerApplied09X15 : highNormUpperX LowerApplied9 15 = LowerApplied09Rows 15 := by decide +kernel
theorem LowerApplied09X16 : highNormUpperX LowerApplied9 16 = LowerApplied09Rows 16 := by decide +kernel
theorem LowerApplied09X17 : highNormUpperX LowerApplied9 17 = LowerApplied09Rows 17 := by decide +kernel
theorem LowerApplied09X18 : highNormUpperX LowerApplied9 18 = LowerApplied09Rows 18 := by decide +kernel
theorem LowerApplied09X19 : highNormUpperX LowerApplied9 19 = LowerApplied09Rows 19 := by decide +kernel
theorem LowerApplied09_rows (x : Fin 20) : highNormUpperX LowerApplied9 x = LowerApplied09Rows x := by
  fin_cases x
  · exact LowerApplied09X0
  · exact LowerApplied09X1
  · exact LowerApplied09X2
  · exact LowerApplied09X3
  · exact LowerApplied09X4
  · exact LowerApplied09X5
  · exact LowerApplied09X6
  · exact LowerApplied09X7
  · exact LowerApplied09X8
  · exact LowerApplied09X9
  · exact LowerApplied09X10
  · exact LowerApplied09X11
  · exact LowerApplied09X12
  · exact LowerApplied09X13
  · exact LowerApplied09X14
  · exact LowerApplied09X15
  · exact LowerApplied09X16
  · exact LowerApplied09X17
  · exact LowerApplied09X18
  · exact LowerApplied09X19
theorem LowerApplied09_bound : highNormUpper LowerApplied9 ≤ 5821753039143851 :=
  highNormUpper_le_of_rows LowerApplied9 LowerApplied09Rows 5821753039143851 LowerApplied09_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
