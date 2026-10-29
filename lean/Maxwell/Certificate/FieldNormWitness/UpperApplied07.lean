import Maxwell.Certificate.AppliedWitness.UpperApplied7
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied07Rows : Fin 20 → ℤ := ![14900351701058, 82675668905833, 94368751855951, 110464580178599, 129935344636638, 30037918284024, 156948958266184, 158868189372164, 156582089651122, 150754878670511, 31395791393321, 161932580200293, 160468706703733, 155002439956750, 145939545213364, 26739040823929, 111753109751698, 93141884720560, 79398936810085, 71322140470186]
theorem UpperApplied07X0 : highNormUpperX UpperApplied7 0 = UpperApplied07Rows 0 := by decide +kernel
theorem UpperApplied07X1 : highNormUpperX UpperApplied7 1 = UpperApplied07Rows 1 := by decide +kernel
theorem UpperApplied07X2 : highNormUpperX UpperApplied7 2 = UpperApplied07Rows 2 := by decide +kernel
theorem UpperApplied07X3 : highNormUpperX UpperApplied7 3 = UpperApplied07Rows 3 := by decide +kernel
theorem UpperApplied07X4 : highNormUpperX UpperApplied7 4 = UpperApplied07Rows 4 := by decide +kernel
theorem UpperApplied07X5 : highNormUpperX UpperApplied7 5 = UpperApplied07Rows 5 := by decide +kernel
theorem UpperApplied07X6 : highNormUpperX UpperApplied7 6 = UpperApplied07Rows 6 := by decide +kernel
theorem UpperApplied07X7 : highNormUpperX UpperApplied7 7 = UpperApplied07Rows 7 := by decide +kernel
theorem UpperApplied07X8 : highNormUpperX UpperApplied7 8 = UpperApplied07Rows 8 := by decide +kernel
theorem UpperApplied07X9 : highNormUpperX UpperApplied7 9 = UpperApplied07Rows 9 := by decide +kernel
theorem UpperApplied07X10 : highNormUpperX UpperApplied7 10 = UpperApplied07Rows 10 := by decide +kernel
theorem UpperApplied07X11 : highNormUpperX UpperApplied7 11 = UpperApplied07Rows 11 := by decide +kernel
theorem UpperApplied07X12 : highNormUpperX UpperApplied7 12 = UpperApplied07Rows 12 := by decide +kernel
theorem UpperApplied07X13 : highNormUpperX UpperApplied7 13 = UpperApplied07Rows 13 := by decide +kernel
theorem UpperApplied07X14 : highNormUpperX UpperApplied7 14 = UpperApplied07Rows 14 := by decide +kernel
theorem UpperApplied07X15 : highNormUpperX UpperApplied7 15 = UpperApplied07Rows 15 := by decide +kernel
theorem UpperApplied07X16 : highNormUpperX UpperApplied7 16 = UpperApplied07Rows 16 := by decide +kernel
theorem UpperApplied07X17 : highNormUpperX UpperApplied7 17 = UpperApplied07Rows 17 := by decide +kernel
theorem UpperApplied07X18 : highNormUpperX UpperApplied7 18 = UpperApplied07Rows 18 := by decide +kernel
theorem UpperApplied07X19 : highNormUpperX UpperApplied7 19 = UpperApplied07Rows 19 := by decide +kernel
theorem UpperApplied07_rows (x : Fin 20) : highNormUpperX UpperApplied7 x = UpperApplied07Rows x := by
  fin_cases x
  · exact UpperApplied07X0
  · exact UpperApplied07X1
  · exact UpperApplied07X2
  · exact UpperApplied07X3
  · exact UpperApplied07X4
  · exact UpperApplied07X5
  · exact UpperApplied07X6
  · exact UpperApplied07X7
  · exact UpperApplied07X8
  · exact UpperApplied07X9
  · exact UpperApplied07X10
  · exact UpperApplied07X11
  · exact UpperApplied07X12
  · exact UpperApplied07X13
  · exact UpperApplied07X14
  · exact UpperApplied07X15
  · exact UpperApplied07X16
  · exact UpperApplied07X17
  · exact UpperApplied07X18
  · exact UpperApplied07X19
theorem UpperApplied07_bound : highNormUpper UpperApplied7 ≤ 2122630907566003 :=
  highNormUpper_le_of_rows UpperApplied7 UpperApplied07Rows 2122630907566003 UpperApplied07_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
