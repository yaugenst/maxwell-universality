import Maxwell.Certificate.AppliedWitness.UpperApplied12
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied12Rows : Fin 20 → ℤ := ![15080777481001, 83673861061997, 95512304123138, 111807513878443, 131519253319863, 30405808415013, 158874447434407, 160822960591731, 158506832531591, 152598364917325, 31780141404788, 163916388469490, 162442578405247, 156907638780620, 147724813285452, 27065840974773, 113109030916139, 94270013421130, 80360007084320, 72183979015183]
theorem UpperApplied12X0 : highNormUpperX UpperApplied12 0 = UpperApplied12Rows 0 := by decide +kernel
theorem UpperApplied12X1 : highNormUpperX UpperApplied12 1 = UpperApplied12Rows 1 := by decide +kernel
theorem UpperApplied12X2 : highNormUpperX UpperApplied12 2 = UpperApplied12Rows 2 := by decide +kernel
theorem UpperApplied12X3 : highNormUpperX UpperApplied12 3 = UpperApplied12Rows 3 := by decide +kernel
theorem UpperApplied12X4 : highNormUpperX UpperApplied12 4 = UpperApplied12Rows 4 := by decide +kernel
theorem UpperApplied12X5 : highNormUpperX UpperApplied12 5 = UpperApplied12Rows 5 := by decide +kernel
theorem UpperApplied12X6 : highNormUpperX UpperApplied12 6 = UpperApplied12Rows 6 := by decide +kernel
theorem UpperApplied12X7 : highNormUpperX UpperApplied12 7 = UpperApplied12Rows 7 := by decide +kernel
theorem UpperApplied12X8 : highNormUpperX UpperApplied12 8 = UpperApplied12Rows 8 := by decide +kernel
theorem UpperApplied12X9 : highNormUpperX UpperApplied12 9 = UpperApplied12Rows 9 := by decide +kernel
theorem UpperApplied12X10 : highNormUpperX UpperApplied12 10 = UpperApplied12Rows 10 := by decide +kernel
theorem UpperApplied12X11 : highNormUpperX UpperApplied12 11 = UpperApplied12Rows 11 := by decide +kernel
theorem UpperApplied12X12 : highNormUpperX UpperApplied12 12 = UpperApplied12Rows 12 := by decide +kernel
theorem UpperApplied12X13 : highNormUpperX UpperApplied12 13 = UpperApplied12Rows 13 := by decide +kernel
theorem UpperApplied12X14 : highNormUpperX UpperApplied12 14 = UpperApplied12Rows 14 := by decide +kernel
theorem UpperApplied12X15 : highNormUpperX UpperApplied12 15 = UpperApplied12Rows 15 := by decide +kernel
theorem UpperApplied12X16 : highNormUpperX UpperApplied12 16 = UpperApplied12Rows 16 := by decide +kernel
theorem UpperApplied12X17 : highNormUpperX UpperApplied12 17 = UpperApplied12Rows 17 := by decide +kernel
theorem UpperApplied12X18 : highNormUpperX UpperApplied12 18 = UpperApplied12Rows 18 := by decide +kernel
theorem UpperApplied12X19 : highNormUpperX UpperApplied12 19 = UpperApplied12Rows 19 := by decide +kernel
theorem UpperApplied12_rows (x : Fin 20) : highNormUpperX UpperApplied12 x = UpperApplied12Rows x := by
  fin_cases x
  · exact UpperApplied12X0
  · exact UpperApplied12X1
  · exact UpperApplied12X2
  · exact UpperApplied12X3
  · exact UpperApplied12X4
  · exact UpperApplied12X5
  · exact UpperApplied12X6
  · exact UpperApplied12X7
  · exact UpperApplied12X8
  · exact UpperApplied12X9
  · exact UpperApplied12X10
  · exact UpperApplied12X11
  · exact UpperApplied12X12
  · exact UpperApplied12X13
  · exact UpperApplied12X14
  · exact UpperApplied12X15
  · exact UpperApplied12X16
  · exact UpperApplied12X17
  · exact UpperApplied12X18
  · exact UpperApplied12X19
theorem UpperApplied12_bound : highNormUpper UpperApplied12 ≤ 2148562555511651 :=
  highNormUpper_le_of_rows UpperApplied12 UpperApplied12Rows 2148562555511651 UpperApplied12_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
