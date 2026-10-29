import Maxwell.Certificate.AppliedWitness.LowerApplied11
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied11Rows : Fin 20 → ℤ := ![40149283038728, 224412731242208, 254869586342419, 298346129333671, 352723562140930, 80945263619969, 426061086959612, 429106416524930, 422923363206344, 409233152640957, 84603815523465, 439577605310878, 433426864661233, 418659269844774, 396173042221046, 72053741689317, 303357233808496, 251557262227509, 214433732611960, 193598547655430]
theorem LowerApplied11X0 : highNormUpperX LowerApplied11 0 = LowerApplied11Rows 0 := by decide +kernel
theorem LowerApplied11X1 : highNormUpperX LowerApplied11 1 = LowerApplied11Rows 1 := by decide +kernel
theorem LowerApplied11X2 : highNormUpperX LowerApplied11 2 = LowerApplied11Rows 2 := by decide +kernel
theorem LowerApplied11X3 : highNormUpperX LowerApplied11 3 = LowerApplied11Rows 3 := by decide +kernel
theorem LowerApplied11X4 : highNormUpperX LowerApplied11 4 = LowerApplied11Rows 4 := by decide +kernel
theorem LowerApplied11X5 : highNormUpperX LowerApplied11 5 = LowerApplied11Rows 5 := by decide +kernel
theorem LowerApplied11X6 : highNormUpperX LowerApplied11 6 = LowerApplied11Rows 6 := by decide +kernel
theorem LowerApplied11X7 : highNormUpperX LowerApplied11 7 = LowerApplied11Rows 7 := by decide +kernel
theorem LowerApplied11X8 : highNormUpperX LowerApplied11 8 = LowerApplied11Rows 8 := by decide +kernel
theorem LowerApplied11X9 : highNormUpperX LowerApplied11 9 = LowerApplied11Rows 9 := by decide +kernel
theorem LowerApplied11X10 : highNormUpperX LowerApplied11 10 = LowerApplied11Rows 10 := by decide +kernel
theorem LowerApplied11X11 : highNormUpperX LowerApplied11 11 = LowerApplied11Rows 11 := by decide +kernel
theorem LowerApplied11X12 : highNormUpperX LowerApplied11 12 = LowerApplied11Rows 12 := by decide +kernel
theorem LowerApplied11X13 : highNormUpperX LowerApplied11 13 = LowerApplied11Rows 13 := by decide +kernel
theorem LowerApplied11X14 : highNormUpperX LowerApplied11 14 = LowerApplied11Rows 14 := by decide +kernel
theorem LowerApplied11X15 : highNormUpperX LowerApplied11 15 = LowerApplied11Rows 15 := by decide +kernel
theorem LowerApplied11X16 : highNormUpperX LowerApplied11 16 = LowerApplied11Rows 16 := by decide +kernel
theorem LowerApplied11X17 : highNormUpperX LowerApplied11 17 = LowerApplied11Rows 17 := by decide +kernel
theorem LowerApplied11X18 : highNormUpperX LowerApplied11 18 = LowerApplied11Rows 18 := by decide +kernel
theorem LowerApplied11X19 : highNormUpperX LowerApplied11 19 = LowerApplied11Rows 19 := by decide +kernel
theorem LowerApplied11_rows (x : Fin 20) : highNormUpperX LowerApplied11 x = LowerApplied11Rows x := by
  fin_cases x
  · exact LowerApplied11X0
  · exact LowerApplied11X1
  · exact LowerApplied11X2
  · exact LowerApplied11X3
  · exact LowerApplied11X4
  · exact LowerApplied11X5
  · exact LowerApplied11X6
  · exact LowerApplied11X7
  · exact LowerApplied11X8
  · exact LowerApplied11X9
  · exact LowerApplied11X10
  · exact LowerApplied11X11
  · exact LowerApplied11X12
  · exact LowerApplied11X13
  · exact LowerApplied11X14
  · exact LowerApplied11X15
  · exact LowerApplied11X16
  · exact LowerApplied11X17
  · exact LowerApplied11X18
  · exact LowerApplied11X19
theorem LowerApplied11_bound : highNormUpper LowerApplied11 ≤ 5746211690603876 :=
  highNormUpper_le_of_rows LowerApplied11 LowerApplied11Rows 5746211690603876 LowerApplied11_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
