import Maxwell.Certificate.AppliedWitness.LowerApplied7
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied07Rows : Fin 20 → ℤ := ![40110984427009, 224201395558009, 254623260371157, 298060483752661, 352395214992942, 80870004987593, 425675071957822, 428706190849085, 422530005864425, 408857760887417, 84525539649466, 439177738572378, 433022471802450, 418270189088090, 395808780414790, 71985729136469, 303073285736471, 251314151603437, 214226122292775, 193415515873001]
theorem LowerApplied07X0 : highNormUpperX LowerApplied7 0 = LowerApplied07Rows 0 := by decide +kernel
theorem LowerApplied07X1 : highNormUpperX LowerApplied7 1 = LowerApplied07Rows 1 := by decide +kernel
theorem LowerApplied07X2 : highNormUpperX LowerApplied7 2 = LowerApplied07Rows 2 := by decide +kernel
theorem LowerApplied07X3 : highNormUpperX LowerApplied7 3 = LowerApplied07Rows 3 := by decide +kernel
theorem LowerApplied07X4 : highNormUpperX LowerApplied7 4 = LowerApplied07Rows 4 := by decide +kernel
theorem LowerApplied07X5 : highNormUpperX LowerApplied7 5 = LowerApplied07Rows 5 := by decide +kernel
theorem LowerApplied07X6 : highNormUpperX LowerApplied7 6 = LowerApplied07Rows 6 := by decide +kernel
theorem LowerApplied07X7 : highNormUpperX LowerApplied7 7 = LowerApplied07Rows 7 := by decide +kernel
theorem LowerApplied07X8 : highNormUpperX LowerApplied7 8 = LowerApplied07Rows 8 := by decide +kernel
theorem LowerApplied07X9 : highNormUpperX LowerApplied7 9 = LowerApplied07Rows 9 := by decide +kernel
theorem LowerApplied07X10 : highNormUpperX LowerApplied7 10 = LowerApplied07Rows 10 := by decide +kernel
theorem LowerApplied07X11 : highNormUpperX LowerApplied7 11 = LowerApplied07Rows 11 := by decide +kernel
theorem LowerApplied07X12 : highNormUpperX LowerApplied7 12 = LowerApplied07Rows 12 := by decide +kernel
theorem LowerApplied07X13 : highNormUpperX LowerApplied7 13 = LowerApplied07Rows 13 := by decide +kernel
theorem LowerApplied07X14 : highNormUpperX LowerApplied7 14 = LowerApplied07Rows 14 := by decide +kernel
theorem LowerApplied07X15 : highNormUpperX LowerApplied7 15 = LowerApplied07Rows 15 := by decide +kernel
theorem LowerApplied07X16 : highNormUpperX LowerApplied7 16 = LowerApplied07Rows 16 := by decide +kernel
theorem LowerApplied07X17 : highNormUpperX LowerApplied7 17 = LowerApplied07Rows 17 := by decide +kernel
theorem LowerApplied07X18 : highNormUpperX LowerApplied7 18 = LowerApplied07Rows 18 := by decide +kernel
theorem LowerApplied07X19 : highNormUpperX LowerApplied7 19 = LowerApplied07Rows 19 := by decide +kernel
theorem LowerApplied07_rows (x : Fin 20) : highNormUpperX LowerApplied7 x = LowerApplied07Rows x := by
  fin_cases x
  · exact LowerApplied07X0
  · exact LowerApplied07X1
  · exact LowerApplied07X2
  · exact LowerApplied07X3
  · exact LowerApplied07X4
  · exact LowerApplied07X5
  · exact LowerApplied07X6
  · exact LowerApplied07X7
  · exact LowerApplied07X8
  · exact LowerApplied07X9
  · exact LowerApplied07X10
  · exact LowerApplied07X11
  · exact LowerApplied07X12
  · exact LowerApplied07X13
  · exact LowerApplied07X14
  · exact LowerApplied07X15
  · exact LowerApplied07X16
  · exact LowerApplied07X17
  · exact LowerApplied07X18
  · exact LowerApplied07X19
theorem LowerApplied07_bound : highNormUpper LowerApplied7 ≤ 5740849897817447 :=
  highNormUpper_le_of_rows LowerApplied7 LowerApplied07Rows 5740849897817447 LowerApplied07_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
