import Maxwell.Certificate.AppliedWitness.LowerApplied23
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied23Rows : Fin 20 → ℤ := ![39912343747986, 223077730552869, 253367142514372, 296596402125600, 350649471506613, 80474913175858, 423580944567026, 426631491184530, 420482251761432, 406839828869288, 84112086395716, 437015693815629, 430926544522488, 416243941986498, 393858379191072, 71632192180437, 301562798064870, 250072840592432, 213165658019871, 192446304530727]
theorem LowerApplied23X0 : highNormUpperX LowerApplied23 0 = LowerApplied23Rows 0 := by decide +kernel
theorem LowerApplied23X1 : highNormUpperX LowerApplied23 1 = LowerApplied23Rows 1 := by decide +kernel
theorem LowerApplied23X2 : highNormUpperX LowerApplied23 2 = LowerApplied23Rows 2 := by decide +kernel
theorem LowerApplied23X3 : highNormUpperX LowerApplied23 3 = LowerApplied23Rows 3 := by decide +kernel
theorem LowerApplied23X4 : highNormUpperX LowerApplied23 4 = LowerApplied23Rows 4 := by decide +kernel
theorem LowerApplied23X5 : highNormUpperX LowerApplied23 5 = LowerApplied23Rows 5 := by decide +kernel
theorem LowerApplied23X6 : highNormUpperX LowerApplied23 6 = LowerApplied23Rows 6 := by decide +kernel
theorem LowerApplied23X7 : highNormUpperX LowerApplied23 7 = LowerApplied23Rows 7 := by decide +kernel
theorem LowerApplied23X8 : highNormUpperX LowerApplied23 8 = LowerApplied23Rows 8 := by decide +kernel
theorem LowerApplied23X9 : highNormUpperX LowerApplied23 9 = LowerApplied23Rows 9 := by decide +kernel
theorem LowerApplied23X10 : highNormUpperX LowerApplied23 10 = LowerApplied23Rows 10 := by decide +kernel
theorem LowerApplied23X11 : highNormUpperX LowerApplied23 11 = LowerApplied23Rows 11 := by decide +kernel
theorem LowerApplied23X12 : highNormUpperX LowerApplied23 12 = LowerApplied23Rows 12 := by decide +kernel
theorem LowerApplied23X13 : highNormUpperX LowerApplied23 13 = LowerApplied23Rows 13 := by decide +kernel
theorem LowerApplied23X14 : highNormUpperX LowerApplied23 14 = LowerApplied23Rows 14 := by decide +kernel
theorem LowerApplied23X15 : highNormUpperX LowerApplied23 15 = LowerApplied23Rows 15 := by decide +kernel
theorem LowerApplied23X16 : highNormUpperX LowerApplied23 16 = LowerApplied23Rows 16 := by decide +kernel
theorem LowerApplied23X17 : highNormUpperX LowerApplied23 17 = LowerApplied23Rows 17 := by decide +kernel
theorem LowerApplied23X18 : highNormUpperX LowerApplied23 18 = LowerApplied23Rows 18 := by decide +kernel
theorem LowerApplied23X19 : highNormUpperX LowerApplied23 19 = LowerApplied23Rows 19 := by decide +kernel
theorem LowerApplied23_rows (x : Fin 20) : highNormUpperX LowerApplied23 x = LowerApplied23Rows x := by
  fin_cases x
  · exact LowerApplied23X0
  · exact LowerApplied23X1
  · exact LowerApplied23X2
  · exact LowerApplied23X3
  · exact LowerApplied23X4
  · exact LowerApplied23X5
  · exact LowerApplied23X6
  · exact LowerApplied23X7
  · exact LowerApplied23X8
  · exact LowerApplied23X9
  · exact LowerApplied23X10
  · exact LowerApplied23X11
  · exact LowerApplied23X12
  · exact LowerApplied23X13
  · exact LowerApplied23X14
  · exact LowerApplied23X15
  · exact LowerApplied23X16
  · exact LowerApplied23X17
  · exact LowerApplied23X18
  · exact LowerApplied23X19
theorem LowerApplied23_bound : highNormUpper LowerApplied23 ≤ 5712648959305314 :=
  highNormUpper_le_of_rows LowerApplied23 LowerApplied23Rows 5712648959305314 LowerApplied23_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
