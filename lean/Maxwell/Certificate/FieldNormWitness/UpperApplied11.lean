import Maxwell.Certificate.AppliedWitness.UpperApplied11
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied11Rows : Fin 20 → ℤ := ![15176756344041, 84203660675894, 96116573725460, 112518990538834, 132362639933254, 30601046816929, 159901444157202, 161860729016126, 159528517014937, 153580796210978, 31983954307081, 164976222692127, 163490608999068, 157919810168125, 148676681066112, 27238597099196, 113829973289039, 94866492036700, 80866196631979, 72645238684718]
theorem UpperApplied11X0 : highNormUpperX UpperApplied11 0 = UpperApplied11Rows 0 := by decide +kernel
theorem UpperApplied11X1 : highNormUpperX UpperApplied11 1 = UpperApplied11Rows 1 := by decide +kernel
theorem UpperApplied11X2 : highNormUpperX UpperApplied11 2 = UpperApplied11Rows 2 := by decide +kernel
theorem UpperApplied11X3 : highNormUpperX UpperApplied11 3 = UpperApplied11Rows 3 := by decide +kernel
theorem UpperApplied11X4 : highNormUpperX UpperApplied11 4 = UpperApplied11Rows 4 := by decide +kernel
theorem UpperApplied11X5 : highNormUpperX UpperApplied11 5 = UpperApplied11Rows 5 := by decide +kernel
theorem UpperApplied11X6 : highNormUpperX UpperApplied11 6 = UpperApplied11Rows 6 := by decide +kernel
theorem UpperApplied11X7 : highNormUpperX UpperApplied11 7 = UpperApplied11Rows 7 := by decide +kernel
theorem UpperApplied11X8 : highNormUpperX UpperApplied11 8 = UpperApplied11Rows 8 := by decide +kernel
theorem UpperApplied11X9 : highNormUpperX UpperApplied11 9 = UpperApplied11Rows 9 := by decide +kernel
theorem UpperApplied11X10 : highNormUpperX UpperApplied11 10 = UpperApplied11Rows 10 := by decide +kernel
theorem UpperApplied11X11 : highNormUpperX UpperApplied11 11 = UpperApplied11Rows 11 := by decide +kernel
theorem UpperApplied11X12 : highNormUpperX UpperApplied11 12 = UpperApplied11Rows 12 := by decide +kernel
theorem UpperApplied11X13 : highNormUpperX UpperApplied11 13 = UpperApplied11Rows 13 := by decide +kernel
theorem UpperApplied11X14 : highNormUpperX UpperApplied11 14 = UpperApplied11Rows 14 := by decide +kernel
theorem UpperApplied11X15 : highNormUpperX UpperApplied11 15 = UpperApplied11Rows 15 := by decide +kernel
theorem UpperApplied11X16 : highNormUpperX UpperApplied11 16 = UpperApplied11Rows 16 := by decide +kernel
theorem UpperApplied11X17 : highNormUpperX UpperApplied11 17 = UpperApplied11Rows 17 := by decide +kernel
theorem UpperApplied11X18 : highNormUpperX UpperApplied11 18 = UpperApplied11Rows 18 := by decide +kernel
theorem UpperApplied11X19 : highNormUpperX UpperApplied11 19 = UpperApplied11Rows 19 := by decide +kernel
theorem UpperApplied11_rows (x : Fin 20) : highNormUpperX UpperApplied11 x = UpperApplied11Rows x := by
  fin_cases x
  · exact UpperApplied11X0
  · exact UpperApplied11X1
  · exact UpperApplied11X2
  · exact UpperApplied11X3
  · exact UpperApplied11X4
  · exact UpperApplied11X5
  · exact UpperApplied11X6
  · exact UpperApplied11X7
  · exact UpperApplied11X8
  · exact UpperApplied11X9
  · exact UpperApplied11X10
  · exact UpperApplied11X11
  · exact UpperApplied11X12
  · exact UpperApplied11X13
  · exact UpperApplied11X14
  · exact UpperApplied11X15
  · exact UpperApplied11X16
  · exact UpperApplied11X17
  · exact UpperApplied11X18
  · exact UpperApplied11X19
theorem UpperApplied11_bound : highNormUpper UpperApplied11 ≤ 2162344929407800 :=
  highNormUpper_le_of_rows UpperApplied11 UpperApplied11Rows 2162344929407800 UpperApplied11_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
