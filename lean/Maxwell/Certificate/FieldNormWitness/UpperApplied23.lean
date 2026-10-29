import Maxwell.Certificate.AppliedWitness.UpperApplied23
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied23Rows : Fin 20 → ℤ := ![15097145993908, 83766275497327, 95614082110642, 111921797651426, 131647642049693, 30435302060424, 159018625217835, 160965603573466, 158647422649661, 152741102187125, 31810645649821, 164066141988442, 162587399735708, 157047174668249, 147863561113629, 27092655605910, 113225427600075, 94370859980683, 80446368916627, 72261624391881]
theorem UpperApplied23X0 : highNormUpperX UpperApplied23 0 = UpperApplied23Rows 0 := by decide +kernel
theorem UpperApplied23X1 : highNormUpperX UpperApplied23 1 = UpperApplied23Rows 1 := by decide +kernel
theorem UpperApplied23X2 : highNormUpperX UpperApplied23 2 = UpperApplied23Rows 2 := by decide +kernel
theorem UpperApplied23X3 : highNormUpperX UpperApplied23 3 = UpperApplied23Rows 3 := by decide +kernel
theorem UpperApplied23X4 : highNormUpperX UpperApplied23 4 = UpperApplied23Rows 4 := by decide +kernel
theorem UpperApplied23X5 : highNormUpperX UpperApplied23 5 = UpperApplied23Rows 5 := by decide +kernel
theorem UpperApplied23X6 : highNormUpperX UpperApplied23 6 = UpperApplied23Rows 6 := by decide +kernel
theorem UpperApplied23X7 : highNormUpperX UpperApplied23 7 = UpperApplied23Rows 7 := by decide +kernel
theorem UpperApplied23X8 : highNormUpperX UpperApplied23 8 = UpperApplied23Rows 8 := by decide +kernel
theorem UpperApplied23X9 : highNormUpperX UpperApplied23 9 = UpperApplied23Rows 9 := by decide +kernel
theorem UpperApplied23X10 : highNormUpperX UpperApplied23 10 = UpperApplied23Rows 10 := by decide +kernel
theorem UpperApplied23X11 : highNormUpperX UpperApplied23 11 = UpperApplied23Rows 11 := by decide +kernel
theorem UpperApplied23X12 : highNormUpperX UpperApplied23 12 = UpperApplied23Rows 12 := by decide +kernel
theorem UpperApplied23X13 : highNormUpperX UpperApplied23 13 = UpperApplied23Rows 13 := by decide +kernel
theorem UpperApplied23X14 : highNormUpperX UpperApplied23 14 = UpperApplied23Rows 14 := by decide +kernel
theorem UpperApplied23X15 : highNormUpperX UpperApplied23 15 = UpperApplied23Rows 15 := by decide +kernel
theorem UpperApplied23X16 : highNormUpperX UpperApplied23 16 = UpperApplied23Rows 16 := by decide +kernel
theorem UpperApplied23X17 : highNormUpperX UpperApplied23 17 = UpperApplied23Rows 17 := by decide +kernel
theorem UpperApplied23X18 : highNormUpperX UpperApplied23 18 = UpperApplied23Rows 18 := by decide +kernel
theorem UpperApplied23X19 : highNormUpperX UpperApplied23 19 = UpperApplied23Rows 19 := by decide +kernel
theorem UpperApplied23_rows (x : Fin 20) : highNormUpperX UpperApplied23 x = UpperApplied23Rows x := by
  fin_cases x
  · exact UpperApplied23X0
  · exact UpperApplied23X1
  · exact UpperApplied23X2
  · exact UpperApplied23X3
  · exact UpperApplied23X4
  · exact UpperApplied23X5
  · exact UpperApplied23X6
  · exact UpperApplied23X7
  · exact UpperApplied23X8
  · exact UpperApplied23X9
  · exact UpperApplied23X10
  · exact UpperApplied23X11
  · exact UpperApplied23X12
  · exact UpperApplied23X13
  · exact UpperApplied23X14
  · exact UpperApplied23X15
  · exact UpperApplied23X16
  · exact UpperApplied23X17
  · exact UpperApplied23X18
  · exact UpperApplied23X19
theorem UpperApplied23_bound : highNormUpper UpperApplied23 ≤ 2150626858642532 :=
  highNormUpper_le_of_rows UpperApplied23 UpperApplied23Rows 2150626858642532 UpperApplied23_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
