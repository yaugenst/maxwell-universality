import Maxwell.Certificate.AppliedWitness.UpperApplied21
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied21Rows : Fin 20 → ℤ := ![15037046071024, 83436488331266, 95239158961123, 111479066664916, 131121348900513, 30311950955031, 158373076690239, 160313642235654, 158006840623847, 152125353321279, 31682265558176, 163401545917952, 161928926172096, 156412526167260, 147266894013969, 26983905380152, 112776502894524, 94001335155150, 80133514169797, 71975454242796]
theorem UpperApplied21X0 : highNormUpperX UpperApplied21 0 = UpperApplied21Rows 0 := by decide +kernel
theorem UpperApplied21X1 : highNormUpperX UpperApplied21 1 = UpperApplied21Rows 1 := by decide +kernel
theorem UpperApplied21X2 : highNormUpperX UpperApplied21 2 = UpperApplied21Rows 2 := by decide +kernel
theorem UpperApplied21X3 : highNormUpperX UpperApplied21 3 = UpperApplied21Rows 3 := by decide +kernel
theorem UpperApplied21X4 : highNormUpperX UpperApplied21 4 = UpperApplied21Rows 4 := by decide +kernel
theorem UpperApplied21X5 : highNormUpperX UpperApplied21 5 = UpperApplied21Rows 5 := by decide +kernel
theorem UpperApplied21X6 : highNormUpperX UpperApplied21 6 = UpperApplied21Rows 6 := by decide +kernel
theorem UpperApplied21X7 : highNormUpperX UpperApplied21 7 = UpperApplied21Rows 7 := by decide +kernel
theorem UpperApplied21X8 : highNormUpperX UpperApplied21 8 = UpperApplied21Rows 8 := by decide +kernel
theorem UpperApplied21X9 : highNormUpperX UpperApplied21 9 = UpperApplied21Rows 9 := by decide +kernel
theorem UpperApplied21X10 : highNormUpperX UpperApplied21 10 = UpperApplied21Rows 10 := by decide +kernel
theorem UpperApplied21X11 : highNormUpperX UpperApplied21 11 = UpperApplied21Rows 11 := by decide +kernel
theorem UpperApplied21X12 : highNormUpperX UpperApplied21 12 = UpperApplied21Rows 12 := by decide +kernel
theorem UpperApplied21X13 : highNormUpperX UpperApplied21 13 = UpperApplied21Rows 13 := by decide +kernel
theorem UpperApplied21X14 : highNormUpperX UpperApplied21 14 = UpperApplied21Rows 14 := by decide +kernel
theorem UpperApplied21X15 : highNormUpperX UpperApplied21 15 = UpperApplied21Rows 15 := by decide +kernel
theorem UpperApplied21X16 : highNormUpperX UpperApplied21 16 = UpperApplied21Rows 16 := by decide +kernel
theorem UpperApplied21X17 : highNormUpperX UpperApplied21 17 = UpperApplied21Rows 17 := by decide +kernel
theorem UpperApplied21X18 : highNormUpperX UpperApplied21 18 = UpperApplied21Rows 18 := by decide +kernel
theorem UpperApplied21X19 : highNormUpperX UpperApplied21 19 = UpperApplied21Rows 19 := by decide +kernel
theorem UpperApplied21_rows (x : Fin 20) : highNormUpperX UpperApplied21 x = UpperApplied21Rows x := by
  fin_cases x
  · exact UpperApplied21X0
  · exact UpperApplied21X1
  · exact UpperApplied21X2
  · exact UpperApplied21X3
  · exact UpperApplied21X4
  · exact UpperApplied21X5
  · exact UpperApplied21X6
  · exact UpperApplied21X7
  · exact UpperApplied21X8
  · exact UpperApplied21X9
  · exact UpperApplied21X10
  · exact UpperApplied21X11
  · exact UpperApplied21X12
  · exact UpperApplied21X13
  · exact UpperApplied21X14
  · exact UpperApplied21X15
  · exact UpperApplied21X16
  · exact UpperApplied21X17
  · exact UpperApplied21X18
  · exact UpperApplied21X19
theorem UpperApplied21_bound : highNormUpper UpperApplied21 ≤ 2142006842426764 :=
  highNormUpper_le_of_rows UpperApplied21 UpperApplied21Rows 2142006842426764 UpperApplied21_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
