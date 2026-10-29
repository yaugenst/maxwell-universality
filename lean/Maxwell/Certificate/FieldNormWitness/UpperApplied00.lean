import Maxwell.Certificate.AppliedWitness.UpperApplied0
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied00Rows : Fin 20 → ℤ := ![15138656336160, 83996661558973, 95875852299012, 112230780806597, 132023064570845, 30521155583903, 159474587962121, 161420261634867, 159094644666383, 153178880936594, 31900636386858, 164537259944322, 163045989510065, 157489575873842, 148286838765918, 27168934169524, 113543871800447, 94629229539783, 80664567725965, 72463344034791]
theorem UpperApplied00X0 : highNormUpperX UpperApplied0 0 = UpperApplied00Rows 0 := by decide +kernel
theorem UpperApplied00X1 : highNormUpperX UpperApplied0 1 = UpperApplied00Rows 1 := by decide +kernel
theorem UpperApplied00X2 : highNormUpperX UpperApplied0 2 = UpperApplied00Rows 2 := by decide +kernel
theorem UpperApplied00X3 : highNormUpperX UpperApplied0 3 = UpperApplied00Rows 3 := by decide +kernel
theorem UpperApplied00X4 : highNormUpperX UpperApplied0 4 = UpperApplied00Rows 4 := by decide +kernel
theorem UpperApplied00X5 : highNormUpperX UpperApplied0 5 = UpperApplied00Rows 5 := by decide +kernel
theorem UpperApplied00X6 : highNormUpperX UpperApplied0 6 = UpperApplied00Rows 6 := by decide +kernel
theorem UpperApplied00X7 : highNormUpperX UpperApplied0 7 = UpperApplied00Rows 7 := by decide +kernel
theorem UpperApplied00X8 : highNormUpperX UpperApplied0 8 = UpperApplied00Rows 8 := by decide +kernel
theorem UpperApplied00X9 : highNormUpperX UpperApplied0 9 = UpperApplied00Rows 9 := by decide +kernel
theorem UpperApplied00X10 : highNormUpperX UpperApplied0 10 = UpperApplied00Rows 10 := by decide +kernel
theorem UpperApplied00X11 : highNormUpperX UpperApplied0 11 = UpperApplied00Rows 11 := by decide +kernel
theorem UpperApplied00X12 : highNormUpperX UpperApplied0 12 = UpperApplied00Rows 12 := by decide +kernel
theorem UpperApplied00X13 : highNormUpperX UpperApplied0 13 = UpperApplied00Rows 13 := by decide +kernel
theorem UpperApplied00X14 : highNormUpperX UpperApplied0 14 = UpperApplied00Rows 14 := by decide +kernel
theorem UpperApplied00X15 : highNormUpperX UpperApplied0 15 = UpperApplied00Rows 15 := by decide +kernel
theorem UpperApplied00X16 : highNormUpperX UpperApplied0 16 = UpperApplied00Rows 16 := by decide +kernel
theorem UpperApplied00X17 : highNormUpperX UpperApplied0 17 = UpperApplied00Rows 17 := by decide +kernel
theorem UpperApplied00X18 : highNormUpperX UpperApplied0 18 = UpperApplied00Rows 18 := by decide +kernel
theorem UpperApplied00X19 : highNormUpperX UpperApplied0 19 = UpperApplied00Rows 19 := by decide +kernel
theorem UpperApplied00_rows (x : Fin 20) : highNormUpperX UpperApplied0 x = UpperApplied00Rows x := by
  fin_cases x
  · exact UpperApplied00X0
  · exact UpperApplied00X1
  · exact UpperApplied00X2
  · exact UpperApplied00X3
  · exact UpperApplied00X4
  · exact UpperApplied00X5
  · exact UpperApplied00X6
  · exact UpperApplied00X7
  · exact UpperApplied00X8
  · exact UpperApplied00X9
  · exact UpperApplied00X10
  · exact UpperApplied00X11
  · exact UpperApplied00X12
  · exact UpperApplied00X13
  · exact UpperApplied00X14
  · exact UpperApplied00X15
  · exact UpperApplied00X16
  · exact UpperApplied00X17
  · exact UpperApplied00X18
  · exact UpperApplied00X19
theorem UpperApplied00_bound : highNormUpper UpperApplied0 ≤ 2156684794106970 :=
  highNormUpper_le_of_rows UpperApplied0 UpperApplied00Rows 2156684794106970 UpperApplied00_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
