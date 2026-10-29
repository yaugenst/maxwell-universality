import Maxwell.Certificate.AppliedWitness.UpperApplied10
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied10Rows : Fin 20 → ℤ := ![15189443922847, 84279674034414, 96200587788006, 112608359134613, 132456442745181, 30621064939739, 159995732122991, 161955407442189, 159623632657902, 153680310697350, 32005438668026, 165074486241391, 163586806031086, 158013098612830, 148771923842597, 27258099397592, 113920147188613, 94949237727357, 80939081548618, 72704973657334]
theorem UpperApplied10X0 : highNormUpperX UpperApplied10 0 = UpperApplied10Rows 0 := by decide +kernel
theorem UpperApplied10X1 : highNormUpperX UpperApplied10 1 = UpperApplied10Rows 1 := by decide +kernel
theorem UpperApplied10X2 : highNormUpperX UpperApplied10 2 = UpperApplied10Rows 2 := by decide +kernel
theorem UpperApplied10X3 : highNormUpperX UpperApplied10 3 = UpperApplied10Rows 3 := by decide +kernel
theorem UpperApplied10X4 : highNormUpperX UpperApplied10 4 = UpperApplied10Rows 4 := by decide +kernel
theorem UpperApplied10X5 : highNormUpperX UpperApplied10 5 = UpperApplied10Rows 5 := by decide +kernel
theorem UpperApplied10X6 : highNormUpperX UpperApplied10 6 = UpperApplied10Rows 6 := by decide +kernel
theorem UpperApplied10X7 : highNormUpperX UpperApplied10 7 = UpperApplied10Rows 7 := by decide +kernel
theorem UpperApplied10X8 : highNormUpperX UpperApplied10 8 = UpperApplied10Rows 8 := by decide +kernel
theorem UpperApplied10X9 : highNormUpperX UpperApplied10 9 = UpperApplied10Rows 9 := by decide +kernel
theorem UpperApplied10X10 : highNormUpperX UpperApplied10 10 = UpperApplied10Rows 10 := by decide +kernel
theorem UpperApplied10X11 : highNormUpperX UpperApplied10 11 = UpperApplied10Rows 11 := by decide +kernel
theorem UpperApplied10X12 : highNormUpperX UpperApplied10 12 = UpperApplied10Rows 12 := by decide +kernel
theorem UpperApplied10X13 : highNormUpperX UpperApplied10 13 = UpperApplied10Rows 13 := by decide +kernel
theorem UpperApplied10X14 : highNormUpperX UpperApplied10 14 = UpperApplied10Rows 14 := by decide +kernel
theorem UpperApplied10X15 : highNormUpperX UpperApplied10 15 = UpperApplied10Rows 15 := by decide +kernel
theorem UpperApplied10X16 : highNormUpperX UpperApplied10 16 = UpperApplied10Rows 16 := by decide +kernel
theorem UpperApplied10X17 : highNormUpperX UpperApplied10 17 = UpperApplied10Rows 17 := by decide +kernel
theorem UpperApplied10X18 : highNormUpperX UpperApplied10 18 = UpperApplied10Rows 18 := by decide +kernel
theorem UpperApplied10X19 : highNormUpperX UpperApplied10 19 = UpperApplied10Rows 19 := by decide +kernel
theorem UpperApplied10_rows (x : Fin 20) : highNormUpperX UpperApplied10 x = UpperApplied10Rows x := by
  fin_cases x
  · exact UpperApplied10X0
  · exact UpperApplied10X1
  · exact UpperApplied10X2
  · exact UpperApplied10X3
  · exact UpperApplied10X4
  · exact UpperApplied10X5
  · exact UpperApplied10X6
  · exact UpperApplied10X7
  · exact UpperApplied10X8
  · exact UpperApplied10X9
  · exact UpperApplied10X10
  · exact UpperApplied10X11
  · exact UpperApplied10X12
  · exact UpperApplied10X13
  · exact UpperApplied10X14
  · exact UpperApplied10X15
  · exact UpperApplied10X16
  · exact UpperApplied10X17
  · exact UpperApplied10X18
  · exact UpperApplied10X19
theorem UpperApplied10_bound : highNormUpper UpperApplied10 ≤ 2163833948400676 :=
  highNormUpper_le_of_rows UpperApplied10 UpperApplied10Rows 2163833948400676 UpperApplied10_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
