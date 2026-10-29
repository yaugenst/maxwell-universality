import Maxwell.Certificate.AppliedWitness.UpperApplied18
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied18Rows : Fin 20 → ℤ := ![14994228764942, 83191352274522, 94962336905455, 111160105761721, 130751510831171, 30228850769142, 157937829214171, 159876130226186, 157573690437605, 151702786729359, 31595077772704, 162951213219714, 161486633268588, 155984296442230, 146858368962608, 26908691237012, 112453107317222, 93727402735313, 79896471258223, 71767737330849]
theorem UpperApplied18X0 : highNormUpperX UpperApplied18 0 = UpperApplied18Rows 0 := by decide +kernel
theorem UpperApplied18X1 : highNormUpperX UpperApplied18 1 = UpperApplied18Rows 1 := by decide +kernel
theorem UpperApplied18X2 : highNormUpperX UpperApplied18 2 = UpperApplied18Rows 2 := by decide +kernel
theorem UpperApplied18X3 : highNormUpperX UpperApplied18 3 = UpperApplied18Rows 3 := by decide +kernel
theorem UpperApplied18X4 : highNormUpperX UpperApplied18 4 = UpperApplied18Rows 4 := by decide +kernel
theorem UpperApplied18X5 : highNormUpperX UpperApplied18 5 = UpperApplied18Rows 5 := by decide +kernel
theorem UpperApplied18X6 : highNormUpperX UpperApplied18 6 = UpperApplied18Rows 6 := by decide +kernel
theorem UpperApplied18X7 : highNormUpperX UpperApplied18 7 = UpperApplied18Rows 7 := by decide +kernel
theorem UpperApplied18X8 : highNormUpperX UpperApplied18 8 = UpperApplied18Rows 8 := by decide +kernel
theorem UpperApplied18X9 : highNormUpperX UpperApplied18 9 = UpperApplied18Rows 9 := by decide +kernel
theorem UpperApplied18X10 : highNormUpperX UpperApplied18 10 = UpperApplied18Rows 10 := by decide +kernel
theorem UpperApplied18X11 : highNormUpperX UpperApplied18 11 = UpperApplied18Rows 11 := by decide +kernel
theorem UpperApplied18X12 : highNormUpperX UpperApplied18 12 = UpperApplied18Rows 12 := by decide +kernel
theorem UpperApplied18X13 : highNormUpperX UpperApplied18 13 = UpperApplied18Rows 13 := by decide +kernel
theorem UpperApplied18X14 : highNormUpperX UpperApplied18 14 = UpperApplied18Rows 14 := by decide +kernel
theorem UpperApplied18X15 : highNormUpperX UpperApplied18 15 = UpperApplied18Rows 15 := by decide +kernel
theorem UpperApplied18X16 : highNormUpperX UpperApplied18 16 = UpperApplied18Rows 16 := by decide +kernel
theorem UpperApplied18X17 : highNormUpperX UpperApplied18 17 = UpperApplied18Rows 17 := by decide +kernel
theorem UpperApplied18X18 : highNormUpperX UpperApplied18 18 = UpperApplied18Rows 18 := by decide +kernel
theorem UpperApplied18X19 : highNormUpperX UpperApplied18 19 = UpperApplied18Rows 19 := by decide +kernel
theorem UpperApplied18_rows (x : Fin 20) : highNormUpperX UpperApplied18 x = UpperApplied18Rows x := by
  fin_cases x
  · exact UpperApplied18X0
  · exact UpperApplied18X1
  · exact UpperApplied18X2
  · exact UpperApplied18X3
  · exact UpperApplied18X4
  · exact UpperApplied18X5
  · exact UpperApplied18X6
  · exact UpperApplied18X7
  · exact UpperApplied18X8
  · exact UpperApplied18X9
  · exact UpperApplied18X10
  · exact UpperApplied18X11
  · exact UpperApplied18X12
  · exact UpperApplied18X13
  · exact UpperApplied18X14
  · exact UpperApplied18X15
  · exact UpperApplied18X16
  · exact UpperApplied18X17
  · exact UpperApplied18X18
  · exact UpperApplied18X19
theorem UpperApplied18_bound : highNormUpper UpperApplied18 ≤ 2136007821458737 :=
  highNormUpper_le_of_rows UpperApplied18 UpperApplied18Rows 2136007821458737 UpperApplied18_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
