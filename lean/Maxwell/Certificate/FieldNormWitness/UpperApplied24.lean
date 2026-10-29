import Maxwell.Certificate.AppliedWitness.UpperApplied24
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied24Rows : Fin 20 → ℤ := ![15032413205407, 83408653696942, 95206379772150, 111447194437624, 131093008493355, 30305300563004, 158353105132466, 160293778703160, 157986182677603, 152100147340472, 31674692442857, 163379636938999, 161908872733666, 156392073953953, 147243292372826, 26976386666081, 112745309785156, 93968779147932, 80103883580810, 71954779231433]
theorem UpperApplied24X0 : highNormUpperX UpperApplied24 0 = UpperApplied24Rows 0 := by decide +kernel
theorem UpperApplied24X1 : highNormUpperX UpperApplied24 1 = UpperApplied24Rows 1 := by decide +kernel
theorem UpperApplied24X2 : highNormUpperX UpperApplied24 2 = UpperApplied24Rows 2 := by decide +kernel
theorem UpperApplied24X3 : highNormUpperX UpperApplied24 3 = UpperApplied24Rows 3 := by decide +kernel
theorem UpperApplied24X4 : highNormUpperX UpperApplied24 4 = UpperApplied24Rows 4 := by decide +kernel
theorem UpperApplied24X5 : highNormUpperX UpperApplied24 5 = UpperApplied24Rows 5 := by decide +kernel
theorem UpperApplied24X6 : highNormUpperX UpperApplied24 6 = UpperApplied24Rows 6 := by decide +kernel
theorem UpperApplied24X7 : highNormUpperX UpperApplied24 7 = UpperApplied24Rows 7 := by decide +kernel
theorem UpperApplied24X8 : highNormUpperX UpperApplied24 8 = UpperApplied24Rows 8 := by decide +kernel
theorem UpperApplied24X9 : highNormUpperX UpperApplied24 9 = UpperApplied24Rows 9 := by decide +kernel
theorem UpperApplied24X10 : highNormUpperX UpperApplied24 10 = UpperApplied24Rows 10 := by decide +kernel
theorem UpperApplied24X11 : highNormUpperX UpperApplied24 11 = UpperApplied24Rows 11 := by decide +kernel
theorem UpperApplied24X12 : highNormUpperX UpperApplied24 12 = UpperApplied24Rows 12 := by decide +kernel
theorem UpperApplied24X13 : highNormUpperX UpperApplied24 13 = UpperApplied24Rows 13 := by decide +kernel
theorem UpperApplied24X14 : highNormUpperX UpperApplied24 14 = UpperApplied24Rows 14 := by decide +kernel
theorem UpperApplied24X15 : highNormUpperX UpperApplied24 15 = UpperApplied24Rows 15 := by decide +kernel
theorem UpperApplied24X16 : highNormUpperX UpperApplied24 16 = UpperApplied24Rows 16 := by decide +kernel
theorem UpperApplied24X17 : highNormUpperX UpperApplied24 17 = UpperApplied24Rows 17 := by decide +kernel
theorem UpperApplied24X18 : highNormUpperX UpperApplied24 18 = UpperApplied24Rows 18 := by decide +kernel
theorem UpperApplied24X19 : highNormUpperX UpperApplied24 19 = UpperApplied24Rows 19 := by decide +kernel
theorem UpperApplied24_rows (x : Fin 20) : highNormUpperX UpperApplied24 x = UpperApplied24Rows x := by
  fin_cases x
  · exact UpperApplied24X0
  · exact UpperApplied24X1
  · exact UpperApplied24X2
  · exact UpperApplied24X3
  · exact UpperApplied24X4
  · exact UpperApplied24X5
  · exact UpperApplied24X6
  · exact UpperApplied24X7
  · exact UpperApplied24X8
  · exact UpperApplied24X9
  · exact UpperApplied24X10
  · exact UpperApplied24X11
  · exact UpperApplied24X12
  · exact UpperApplied24X13
  · exact UpperApplied24X14
  · exact UpperApplied24X15
  · exact UpperApplied24X16
  · exact UpperApplied24X17
  · exact UpperApplied24X18
  · exact UpperApplied24X19
theorem UpperApplied24_bound : highNormUpper UpperApplied24 ≤ 2141573870875896 :=
  highNormUpper_le_of_rows UpperApplied24 UpperApplied24Rows 2141573870875896 UpperApplied24_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
