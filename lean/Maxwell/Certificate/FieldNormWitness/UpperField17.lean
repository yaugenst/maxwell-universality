import Maxwell.Certificate.ProjectionWitness.UpperResult17
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField17Rows : Fin 20 → ℤ := ![17619428050138986798006551944163, 3127372188124212019660514196776, 25777729652517196986214394284755, 964277830104458498739177185415, 459719748579062464027002378807, 171190426039439264070407046065, 46006213581400327356819508637, 31189507524542415137397115770, 5441605815546334935489741313, 6742472230877950668645970154, 6742472230877890863345262154, 5441605815546221396264189725, 31189507524542111937075305961, 46006213581400312651734966950, 171190426039437608407625526788, 459719748579059076281748283729, 964277830104446448690965527344, 25777729652516885640197782492570, 3127372188124172089628098727645, 17619428050138726489589853742927]
theorem UpperField17X0 : highNormUpperX UpperResult17 0 = UpperField17Rows 0 := by decide +kernel
theorem UpperField17X1 : highNormUpperX UpperResult17 1 = UpperField17Rows 1 := by decide +kernel
theorem UpperField17X2 : highNormUpperX UpperResult17 2 = UpperField17Rows 2 := by decide +kernel
theorem UpperField17X3 : highNormUpperX UpperResult17 3 = UpperField17Rows 3 := by decide +kernel
theorem UpperField17X4 : highNormUpperX UpperResult17 4 = UpperField17Rows 4 := by decide +kernel
theorem UpperField17X5 : highNormUpperX UpperResult17 5 = UpperField17Rows 5 := by decide +kernel
theorem UpperField17X6 : highNormUpperX UpperResult17 6 = UpperField17Rows 6 := by decide +kernel
theorem UpperField17X7 : highNormUpperX UpperResult17 7 = UpperField17Rows 7 := by decide +kernel
theorem UpperField17X8 : highNormUpperX UpperResult17 8 = UpperField17Rows 8 := by decide +kernel
theorem UpperField17X9 : highNormUpperX UpperResult17 9 = UpperField17Rows 9 := by decide +kernel
theorem UpperField17X10 : highNormUpperX UpperResult17 10 = UpperField17Rows 10 := by decide +kernel
theorem UpperField17X11 : highNormUpperX UpperResult17 11 = UpperField17Rows 11 := by decide +kernel
theorem UpperField17X12 : highNormUpperX UpperResult17 12 = UpperField17Rows 12 := by decide +kernel
theorem UpperField17X13 : highNormUpperX UpperResult17 13 = UpperField17Rows 13 := by decide +kernel
theorem UpperField17X14 : highNormUpperX UpperResult17 14 = UpperField17Rows 14 := by decide +kernel
theorem UpperField17X15 : highNormUpperX UpperResult17 15 = UpperField17Rows 15 := by decide +kernel
theorem UpperField17X16 : highNormUpperX UpperResult17 16 = UpperField17Rows 16 := by decide +kernel
theorem UpperField17X17 : highNormUpperX UpperResult17 17 = UpperField17Rows 17 := by decide +kernel
theorem UpperField17X18 : highNormUpperX UpperResult17 18 = UpperField17Rows 18 := by decide +kernel
theorem UpperField17X19 : highNormUpperX UpperResult17 19 = UpperField17Rows 19 := by decide +kernel
theorem UpperField17_rows (x : Fin 20) : highNormUpperX UpperResult17 x = UpperField17Rows x := by
  fin_cases x
  · exact UpperField17X0
  · exact UpperField17X1
  · exact UpperField17X2
  · exact UpperField17X3
  · exact UpperField17X4
  · exact UpperField17X5
  · exact UpperField17X6
  · exact UpperField17X7
  · exact UpperField17X8
  · exact UpperField17X9
  · exact UpperField17X10
  · exact UpperField17X11
  · exact UpperField17X12
  · exact UpperField17X13
  · exact UpperField17X14
  · exact UpperField17X15
  · exact UpperField17X16
  · exact UpperField17X17
  · exact UpperField17X18
  · exact UpperField17X19
theorem UpperField17_bound : highNormUpper UpperResult17 ≤ 96418195389310816948460893397648 :=
  highNormUpper_le_of_rows UpperResult17 UpperField17Rows 96418195389310816948460893397648 UpperField17_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
