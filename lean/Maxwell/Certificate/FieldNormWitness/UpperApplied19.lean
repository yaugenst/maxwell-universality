import Maxwell.Certificate.AppliedWitness.UpperApplied19
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied19Rows : Fin 20 → ℤ := ![14491920485142, 80405279941827, 91780543503556, 107437099773351, 126377665445430, 29217560641143, 152659597533212, 154531626671668, 152306102547783, 146631205285810, 30538276196952, 157506498096356, 156087933884299, 150768635031377, 141948230307399, 26008104432619, 108688229102568, 90587348759130, 77220100753127, 69364862715004]
theorem UpperApplied19X0 : highNormUpperX UpperApplied19 0 = UpperApplied19Rows 0 := by decide +kernel
theorem UpperApplied19X1 : highNormUpperX UpperApplied19 1 = UpperApplied19Rows 1 := by decide +kernel
theorem UpperApplied19X2 : highNormUpperX UpperApplied19 2 = UpperApplied19Rows 2 := by decide +kernel
theorem UpperApplied19X3 : highNormUpperX UpperApplied19 3 = UpperApplied19Rows 3 := by decide +kernel
theorem UpperApplied19X4 : highNormUpperX UpperApplied19 4 = UpperApplied19Rows 4 := by decide +kernel
theorem UpperApplied19X5 : highNormUpperX UpperApplied19 5 = UpperApplied19Rows 5 := by decide +kernel
theorem UpperApplied19X6 : highNormUpperX UpperApplied19 6 = UpperApplied19Rows 6 := by decide +kernel
theorem UpperApplied19X7 : highNormUpperX UpperApplied19 7 = UpperApplied19Rows 7 := by decide +kernel
theorem UpperApplied19X8 : highNormUpperX UpperApplied19 8 = UpperApplied19Rows 8 := by decide +kernel
theorem UpperApplied19X9 : highNormUpperX UpperApplied19 9 = UpperApplied19Rows 9 := by decide +kernel
theorem UpperApplied19X10 : highNormUpperX UpperApplied19 10 = UpperApplied19Rows 10 := by decide +kernel
theorem UpperApplied19X11 : highNormUpperX UpperApplied19 11 = UpperApplied19Rows 11 := by decide +kernel
theorem UpperApplied19X12 : highNormUpperX UpperApplied19 12 = UpperApplied19Rows 12 := by decide +kernel
theorem UpperApplied19X13 : highNormUpperX UpperApplied19 13 = UpperApplied19Rows 13 := by decide +kernel
theorem UpperApplied19X14 : highNormUpperX UpperApplied19 14 = UpperApplied19Rows 14 := by decide +kernel
theorem UpperApplied19X15 : highNormUpperX UpperApplied19 15 = UpperApplied19Rows 15 := by decide +kernel
theorem UpperApplied19X16 : highNormUpperX UpperApplied19 16 = UpperApplied19Rows 16 := by decide +kernel
theorem UpperApplied19X17 : highNormUpperX UpperApplied19 17 = UpperApplied19Rows 17 := by decide +kernel
theorem UpperApplied19X18 : highNormUpperX UpperApplied19 18 = UpperApplied19Rows 18 := by decide +kernel
theorem UpperApplied19X19 : highNormUpperX UpperApplied19 19 = UpperApplied19Rows 19 := by decide +kernel
theorem UpperApplied19_rows (x : Fin 20) : highNormUpperX UpperApplied19 x = UpperApplied19Rows x := by
  fin_cases x
  · exact UpperApplied19X0
  · exact UpperApplied19X1
  · exact UpperApplied19X2
  · exact UpperApplied19X3
  · exact UpperApplied19X4
  · exact UpperApplied19X5
  · exact UpperApplied19X6
  · exact UpperApplied19X7
  · exact UpperApplied19X8
  · exact UpperApplied19X9
  · exact UpperApplied19X10
  · exact UpperApplied19X11
  · exact UpperApplied19X12
  · exact UpperApplied19X13
  · exact UpperApplied19X14
  · exact UpperApplied19X15
  · exact UpperApplied19X16
  · exact UpperApplied19X17
  · exact UpperApplied19X18
  · exact UpperApplied19X19
theorem UpperApplied19_bound : highNormUpper UpperApplied19 ≤ 2064556821107753 :=
  highNormUpper_le_of_rows UpperApplied19 UpperApplied19Rows 2064556821107753 UpperApplied19_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
