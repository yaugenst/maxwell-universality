import Maxwell.Certificate.AppliedWitness.UpperApplied4
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied04Rows : Fin 20 → ℤ := ![15274496257574, 84745415993714, 96730062141898, 113231480167392, 133195236669851, 30793205121019, 160892777675588, 162862386145455, 160516890763309, 154540575008098, 32185136881149, 166001815919037, 164502770399373, 158897404998284, 149604239622134, 27411387655684, 114552466860092, 95472451083879, 81384769284361, 73109790819095]
theorem UpperApplied04X0 : highNormUpperX UpperApplied4 0 = UpperApplied04Rows 0 := by decide +kernel
theorem UpperApplied04X1 : highNormUpperX UpperApplied4 1 = UpperApplied04Rows 1 := by decide +kernel
theorem UpperApplied04X2 : highNormUpperX UpperApplied4 2 = UpperApplied04Rows 2 := by decide +kernel
theorem UpperApplied04X3 : highNormUpperX UpperApplied4 3 = UpperApplied04Rows 3 := by decide +kernel
theorem UpperApplied04X4 : highNormUpperX UpperApplied4 4 = UpperApplied04Rows 4 := by decide +kernel
theorem UpperApplied04X5 : highNormUpperX UpperApplied4 5 = UpperApplied04Rows 5 := by decide +kernel
theorem UpperApplied04X6 : highNormUpperX UpperApplied4 6 = UpperApplied04Rows 6 := by decide +kernel
theorem UpperApplied04X7 : highNormUpperX UpperApplied4 7 = UpperApplied04Rows 7 := by decide +kernel
theorem UpperApplied04X8 : highNormUpperX UpperApplied4 8 = UpperApplied04Rows 8 := by decide +kernel
theorem UpperApplied04X9 : highNormUpperX UpperApplied4 9 = UpperApplied04Rows 9 := by decide +kernel
theorem UpperApplied04X10 : highNormUpperX UpperApplied4 10 = UpperApplied04Rows 10 := by decide +kernel
theorem UpperApplied04X11 : highNormUpperX UpperApplied4 11 = UpperApplied04Rows 11 := by decide +kernel
theorem UpperApplied04X12 : highNormUpperX UpperApplied4 12 = UpperApplied04Rows 12 := by decide +kernel
theorem UpperApplied04X13 : highNormUpperX UpperApplied4 13 = UpperApplied04Rows 13 := by decide +kernel
theorem UpperApplied04X14 : highNormUpperX UpperApplied4 14 = UpperApplied04Rows 14 := by decide +kernel
theorem UpperApplied04X15 : highNormUpperX UpperApplied4 15 = UpperApplied04Rows 15 := by decide +kernel
theorem UpperApplied04X16 : highNormUpperX UpperApplied4 16 = UpperApplied04Rows 16 := by decide +kernel
theorem UpperApplied04X17 : highNormUpperX UpperApplied4 17 = UpperApplied04Rows 17 := by decide +kernel
theorem UpperApplied04X18 : highNormUpperX UpperApplied4 18 = UpperApplied04Rows 18 := by decide +kernel
theorem UpperApplied04X19 : highNormUpperX UpperApplied4 19 = UpperApplied04Rows 19 := by decide +kernel
theorem UpperApplied04_rows (x : Fin 20) : highNormUpperX UpperApplied4 x = UpperApplied04Rows x := by
  fin_cases x
  · exact UpperApplied04X0
  · exact UpperApplied04X1
  · exact UpperApplied04X2
  · exact UpperApplied04X3
  · exact UpperApplied04X4
  · exact UpperApplied04X5
  · exact UpperApplied04X6
  · exact UpperApplied04X7
  · exact UpperApplied04X8
  · exact UpperApplied04X9
  · exact UpperApplied04X10
  · exact UpperApplied04X11
  · exact UpperApplied04X12
  · exact UpperApplied04X13
  · exact UpperApplied04X14
  · exact UpperApplied04X15
  · exact UpperApplied04X16
  · exact UpperApplied04X17
  · exact UpperApplied04X18
  · exact UpperApplied04X19
theorem UpperApplied04_bound : highNormUpper UpperApplied4 ≤ 2175904759466986 :=
  highNormUpper_le_of_rows UpperApplied4 UpperApplied04Rows 2175904759466986 UpperApplied04_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
