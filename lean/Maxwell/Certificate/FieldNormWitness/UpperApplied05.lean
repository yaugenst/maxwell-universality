import Maxwell.Certificate.AppliedWitness.UpperApplied5
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied05Rows : Fin 20 → ℤ := ![15352077086624, 85183462607143, 97232408960105, 113820000588271, 133885088189493, 30952532983501, 161729940037931, 163710940555921, 161353971995913, 155342573421725, 32351531718101, 166865474547376, 165359856206606, 159725703697257, 150381601027050, 27552192774854, 115145081037634, 95968085639020, 81807781825686, 73484244719710]
theorem UpperApplied05X0 : highNormUpperX UpperApplied5 0 = UpperApplied05Rows 0 := by decide +kernel
theorem UpperApplied05X1 : highNormUpperX UpperApplied5 1 = UpperApplied05Rows 1 := by decide +kernel
theorem UpperApplied05X2 : highNormUpperX UpperApplied5 2 = UpperApplied05Rows 2 := by decide +kernel
theorem UpperApplied05X3 : highNormUpperX UpperApplied5 3 = UpperApplied05Rows 3 := by decide +kernel
theorem UpperApplied05X4 : highNormUpperX UpperApplied5 4 = UpperApplied05Rows 4 := by decide +kernel
theorem UpperApplied05X5 : highNormUpperX UpperApplied5 5 = UpperApplied05Rows 5 := by decide +kernel
theorem UpperApplied05X6 : highNormUpperX UpperApplied5 6 = UpperApplied05Rows 6 := by decide +kernel
theorem UpperApplied05X7 : highNormUpperX UpperApplied5 7 = UpperApplied05Rows 7 := by decide +kernel
theorem UpperApplied05X8 : highNormUpperX UpperApplied5 8 = UpperApplied05Rows 8 := by decide +kernel
theorem UpperApplied05X9 : highNormUpperX UpperApplied5 9 = UpperApplied05Rows 9 := by decide +kernel
theorem UpperApplied05X10 : highNormUpperX UpperApplied5 10 = UpperApplied05Rows 10 := by decide +kernel
theorem UpperApplied05X11 : highNormUpperX UpperApplied5 11 = UpperApplied05Rows 11 := by decide +kernel
theorem UpperApplied05X12 : highNormUpperX UpperApplied5 12 = UpperApplied05Rows 12 := by decide +kernel
theorem UpperApplied05X13 : highNormUpperX UpperApplied5 13 = UpperApplied05Rows 13 := by decide +kernel
theorem UpperApplied05X14 : highNormUpperX UpperApplied5 14 = UpperApplied05Rows 14 := by decide +kernel
theorem UpperApplied05X15 : highNormUpperX UpperApplied5 15 = UpperApplied05Rows 15 := by decide +kernel
theorem UpperApplied05X16 : highNormUpperX UpperApplied5 16 = UpperApplied05Rows 16 := by decide +kernel
theorem UpperApplied05X17 : highNormUpperX UpperApplied5 17 = UpperApplied05Rows 17 := by decide +kernel
theorem UpperApplied05X18 : highNormUpperX UpperApplied5 18 = UpperApplied05Rows 18 := by decide +kernel
theorem UpperApplied05X19 : highNormUpperX UpperApplied5 19 = UpperApplied05Rows 19 := by decide +kernel
theorem UpperApplied05_rows (x : Fin 20) : highNormUpperX UpperApplied5 x = UpperApplied05Rows x := by
  fin_cases x
  · exact UpperApplied05X0
  · exact UpperApplied05X1
  · exact UpperApplied05X2
  · exact UpperApplied05X3
  · exact UpperApplied05X4
  · exact UpperApplied05X5
  · exact UpperApplied05X6
  · exact UpperApplied05X7
  · exact UpperApplied05X8
  · exact UpperApplied05X9
  · exact UpperApplied05X10
  · exact UpperApplied05X11
  · exact UpperApplied05X12
  · exact UpperApplied05X13
  · exact UpperApplied05X14
  · exact UpperApplied05X15
  · exact UpperApplied05X16
  · exact UpperApplied05X17
  · exact UpperApplied05X18
  · exact UpperApplied05X19
theorem UpperApplied05_bound : highNormUpper UpperApplied5 ≤ 2187204549619921 :=
  highNormUpper_le_of_rows UpperApplied5 UpperApplied05Rows 2187204549619921 UpperApplied05_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
