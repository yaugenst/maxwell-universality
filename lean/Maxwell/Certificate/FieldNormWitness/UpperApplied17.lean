import Maxwell.Certificate.AppliedWitness.UpperApplied17
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied17Rows : Fin 20 → ℤ := ![14967518862038, 83044687727775, 94795226188830, 110975417771195, 130551422124087, 30184194303688, 157724447378046, 159660779435453, 157358120217128, 151485267005220, 31547879392179, 162729918288111, 161268453524848, 155770901657148, 146649677950359, 26865897703093, 112267472417381, 93562634559026, 79755735712135, 71644380754533]
theorem UpperApplied17X0 : highNormUpperX UpperApplied17 0 = UpperApplied17Rows 0 := by decide +kernel
theorem UpperApplied17X1 : highNormUpperX UpperApplied17 1 = UpperApplied17Rows 1 := by decide +kernel
theorem UpperApplied17X2 : highNormUpperX UpperApplied17 2 = UpperApplied17Rows 2 := by decide +kernel
theorem UpperApplied17X3 : highNormUpperX UpperApplied17 3 = UpperApplied17Rows 3 := by decide +kernel
theorem UpperApplied17X4 : highNormUpperX UpperApplied17 4 = UpperApplied17Rows 4 := by decide +kernel
theorem UpperApplied17X5 : highNormUpperX UpperApplied17 5 = UpperApplied17Rows 5 := by decide +kernel
theorem UpperApplied17X6 : highNormUpperX UpperApplied17 6 = UpperApplied17Rows 6 := by decide +kernel
theorem UpperApplied17X7 : highNormUpperX UpperApplied17 7 = UpperApplied17Rows 7 := by decide +kernel
theorem UpperApplied17X8 : highNormUpperX UpperApplied17 8 = UpperApplied17Rows 8 := by decide +kernel
theorem UpperApplied17X9 : highNormUpperX UpperApplied17 9 = UpperApplied17Rows 9 := by decide +kernel
theorem UpperApplied17X10 : highNormUpperX UpperApplied17 10 = UpperApplied17Rows 10 := by decide +kernel
theorem UpperApplied17X11 : highNormUpperX UpperApplied17 11 = UpperApplied17Rows 11 := by decide +kernel
theorem UpperApplied17X12 : highNormUpperX UpperApplied17 12 = UpperApplied17Rows 12 := by decide +kernel
theorem UpperApplied17X13 : highNormUpperX UpperApplied17 13 = UpperApplied17Rows 13 := by decide +kernel
theorem UpperApplied17X14 : highNormUpperX UpperApplied17 14 = UpperApplied17Rows 14 := by decide +kernel
theorem UpperApplied17X15 : highNormUpperX UpperApplied17 15 = UpperApplied17Rows 15 := by decide +kernel
theorem UpperApplied17X16 : highNormUpperX UpperApplied17 16 = UpperApplied17Rows 16 := by decide +kernel
theorem UpperApplied17X17 : highNormUpperX UpperApplied17 17 = UpperApplied17Rows 17 := by decide +kernel
theorem UpperApplied17X18 : highNormUpperX UpperApplied17 18 = UpperApplied17Rows 18 := by decide +kernel
theorem UpperApplied17X19 : highNormUpperX UpperApplied17 19 = UpperApplied17Rows 19 := by decide +kernel
theorem UpperApplied17_rows (x : Fin 20) : highNormUpperX UpperApplied17 x = UpperApplied17Rows x := by
  fin_cases x
  · exact UpperApplied17X0
  · exact UpperApplied17X1
  · exact UpperApplied17X2
  · exact UpperApplied17X3
  · exact UpperApplied17X4
  · exact UpperApplied17X5
  · exact UpperApplied17X6
  · exact UpperApplied17X7
  · exact UpperApplied17X8
  · exact UpperApplied17X9
  · exact UpperApplied17X10
  · exact UpperApplied17X11
  · exact UpperApplied17X12
  · exact UpperApplied17X13
  · exact UpperApplied17X14
  · exact UpperApplied17X15
  · exact UpperApplied17X16
  · exact UpperApplied17X17
  · exact UpperApplied17X18
  · exact UpperApplied17X19
theorem UpperApplied17_bound : highNormUpper UpperApplied17 ≤ 2132810032972273 :=
  highNormUpper_le_of_rows UpperApplied17 UpperApplied17Rows 2132810032972273 UpperApplied17_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
