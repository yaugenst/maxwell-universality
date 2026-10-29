import Maxwell.Certificate.AppliedWitness.UpperApplied6
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied06Rows : Fin 20 → ℤ := ![15202370198633, 84346859466936, 96278295502140, 112700977871775, 132574628040407, 30648598719743, 160142397872973, 162099569483518, 159764173837956, 153819740094086, 32033582992926, 165225406114269, 163732198636949, 158152560966989, 148908236302152, 27281812209511, 114017679604165, 95026588907432, 81002172031502, 72767203443989]
theorem UpperApplied06X0 : highNormUpperX UpperApplied6 0 = UpperApplied06Rows 0 := by decide +kernel
theorem UpperApplied06X1 : highNormUpperX UpperApplied6 1 = UpperApplied06Rows 1 := by decide +kernel
theorem UpperApplied06X2 : highNormUpperX UpperApplied6 2 = UpperApplied06Rows 2 := by decide +kernel
theorem UpperApplied06X3 : highNormUpperX UpperApplied6 3 = UpperApplied06Rows 3 := by decide +kernel
theorem UpperApplied06X4 : highNormUpperX UpperApplied6 4 = UpperApplied06Rows 4 := by decide +kernel
theorem UpperApplied06X5 : highNormUpperX UpperApplied6 5 = UpperApplied06Rows 5 := by decide +kernel
theorem UpperApplied06X6 : highNormUpperX UpperApplied6 6 = UpperApplied06Rows 6 := by decide +kernel
theorem UpperApplied06X7 : highNormUpperX UpperApplied6 7 = UpperApplied06Rows 7 := by decide +kernel
theorem UpperApplied06X8 : highNormUpperX UpperApplied6 8 = UpperApplied06Rows 8 := by decide +kernel
theorem UpperApplied06X9 : highNormUpperX UpperApplied6 9 = UpperApplied06Rows 9 := by decide +kernel
theorem UpperApplied06X10 : highNormUpperX UpperApplied6 10 = UpperApplied06Rows 10 := by decide +kernel
theorem UpperApplied06X11 : highNormUpperX UpperApplied6 11 = UpperApplied06Rows 11 := by decide +kernel
theorem UpperApplied06X12 : highNormUpperX UpperApplied6 12 = UpperApplied06Rows 12 := by decide +kernel
theorem UpperApplied06X13 : highNormUpperX UpperApplied6 13 = UpperApplied06Rows 13 := by decide +kernel
theorem UpperApplied06X14 : highNormUpperX UpperApplied6 14 = UpperApplied06Rows 14 := by decide +kernel
theorem UpperApplied06X15 : highNormUpperX UpperApplied6 15 = UpperApplied06Rows 15 := by decide +kernel
theorem UpperApplied06X16 : highNormUpperX UpperApplied6 16 = UpperApplied06Rows 16 := by decide +kernel
theorem UpperApplied06X17 : highNormUpperX UpperApplied6 17 = UpperApplied06Rows 17 := by decide +kernel
theorem UpperApplied06X18 : highNormUpperX UpperApplied6 18 = UpperApplied06Rows 18 := by decide +kernel
theorem UpperApplied06X19 : highNormUpperX UpperApplied6 19 = UpperApplied06Rows 19 := by decide +kernel
theorem UpperApplied06_rows (x : Fin 20) : highNormUpperX UpperApplied6 x = UpperApplied06Rows x := by
  fin_cases x
  · exact UpperApplied06X0
  · exact UpperApplied06X1
  · exact UpperApplied06X2
  · exact UpperApplied06X3
  · exact UpperApplied06X4
  · exact UpperApplied06X5
  · exact UpperApplied06X6
  · exact UpperApplied06X7
  · exact UpperApplied06X8
  · exact UpperApplied06X9
  · exact UpperApplied06X10
  · exact UpperApplied06X11
  · exact UpperApplied06X12
  · exact UpperApplied06X13
  · exact UpperApplied06X14
  · exact UpperApplied06X15
  · exact UpperApplied06X16
  · exact UpperApplied06X17
  · exact UpperApplied06X18
  · exact UpperApplied06X19
theorem UpperApplied06_bound : highNormUpper UpperApplied6 ≤ 2165725052298051 :=
  highNormUpper_le_of_rows UpperApplied6 UpperApplied06Rows 2165725052298051 UpperApplied06_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
