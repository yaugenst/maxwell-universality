import Maxwell.Certificate.AppliedWitness.UpperApplied8
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied08Rows : Fin 20 → ℤ := ![15199732058106, 84335332085512, 96266801082003, 112690242621605, 132556729961727, 30645498548302, 160125896797367, 162091403868069, 159756304302545, 153801492621598, 32030093804851, 165209333516187, 163724087858781, 158144597923946, 148889450433690, 27278774999634, 114001448315738, 95015144159119, 80993618212070, 72755156529415]
theorem UpperApplied08X0 : highNormUpperX UpperApplied8 0 = UpperApplied08Rows 0 := by decide +kernel
theorem UpperApplied08X1 : highNormUpperX UpperApplied8 1 = UpperApplied08Rows 1 := by decide +kernel
theorem UpperApplied08X2 : highNormUpperX UpperApplied8 2 = UpperApplied08Rows 2 := by decide +kernel
theorem UpperApplied08X3 : highNormUpperX UpperApplied8 3 = UpperApplied08Rows 3 := by decide +kernel
theorem UpperApplied08X4 : highNormUpperX UpperApplied8 4 = UpperApplied08Rows 4 := by decide +kernel
theorem UpperApplied08X5 : highNormUpperX UpperApplied8 5 = UpperApplied08Rows 5 := by decide +kernel
theorem UpperApplied08X6 : highNormUpperX UpperApplied8 6 = UpperApplied08Rows 6 := by decide +kernel
theorem UpperApplied08X7 : highNormUpperX UpperApplied8 7 = UpperApplied08Rows 7 := by decide +kernel
theorem UpperApplied08X8 : highNormUpperX UpperApplied8 8 = UpperApplied08Rows 8 := by decide +kernel
theorem UpperApplied08X9 : highNormUpperX UpperApplied8 9 = UpperApplied08Rows 9 := by decide +kernel
theorem UpperApplied08X10 : highNormUpperX UpperApplied8 10 = UpperApplied08Rows 10 := by decide +kernel
theorem UpperApplied08X11 : highNormUpperX UpperApplied8 11 = UpperApplied08Rows 11 := by decide +kernel
theorem UpperApplied08X12 : highNormUpperX UpperApplied8 12 = UpperApplied08Rows 12 := by decide +kernel
theorem UpperApplied08X13 : highNormUpperX UpperApplied8 13 = UpperApplied08Rows 13 := by decide +kernel
theorem UpperApplied08X14 : highNormUpperX UpperApplied8 14 = UpperApplied08Rows 14 := by decide +kernel
theorem UpperApplied08X15 : highNormUpperX UpperApplied8 15 = UpperApplied08Rows 15 := by decide +kernel
theorem UpperApplied08X16 : highNormUpperX UpperApplied8 16 = UpperApplied08Rows 16 := by decide +kernel
theorem UpperApplied08X17 : highNormUpperX UpperApplied8 17 = UpperApplied08Rows 17 := by decide +kernel
theorem UpperApplied08X18 : highNormUpperX UpperApplied8 18 = UpperApplied08Rows 18 := by decide +kernel
theorem UpperApplied08X19 : highNormUpperX UpperApplied8 19 = UpperApplied08Rows 19 := by decide +kernel
theorem UpperApplied08_rows (x : Fin 20) : highNormUpperX UpperApplied8 x = UpperApplied08Rows x := by
  fin_cases x
  · exact UpperApplied08X0
  · exact UpperApplied08X1
  · exact UpperApplied08X2
  · exact UpperApplied08X3
  · exact UpperApplied08X4
  · exact UpperApplied08X5
  · exact UpperApplied08X6
  · exact UpperApplied08X7
  · exact UpperApplied08X8
  · exact UpperApplied08X9
  · exact UpperApplied08X10
  · exact UpperApplied08X11
  · exact UpperApplied08X12
  · exact UpperApplied08X13
  · exact UpperApplied08X14
  · exact UpperApplied08X15
  · exact UpperApplied08X16
  · exact UpperApplied08X17
  · exact UpperApplied08X18
  · exact UpperApplied08X19
theorem UpperApplied08_bound : highNormUpper UpperApplied8 ≤ 2165511139700265 :=
  highNormUpper_le_of_rows UpperApplied8 UpperApplied08Rows 2165511139700265 UpperApplied08_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
