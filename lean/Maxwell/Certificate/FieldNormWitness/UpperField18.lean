import Maxwell.Certificate.ProjectionWitness.UpperResult18
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField18Rows : Fin 20 → ℤ := ![16517748274262741015375816793299, 20474032238144093363587823093213, 10280377124109617052076524916171, 579831735683006737286582316711, 205571423520204163845570563672, 77372890730967761201216275152, 35016361342334450301741502434, 21146809840207013678607196501, 12939194357077017535009699888, 5061642665321117142807062766, 5061642665321268611210701939, 12939194357077485632454946649, 21146809840207138864773210700, 35016361342334914969970584969, 77372890730967079753244959810, 205571423520202767877595688149, 579831735683004591731784857308, 10280377124109509802986754377581, 20474032238143924330681808968769, 16517748274262821364603303730754]
theorem UpperField18X0 : highNormUpperX UpperResult18 0 = UpperField18Rows 0 := by decide +kernel
theorem UpperField18X1 : highNormUpperX UpperResult18 1 = UpperField18Rows 1 := by decide +kernel
theorem UpperField18X2 : highNormUpperX UpperResult18 2 = UpperField18Rows 2 := by decide +kernel
theorem UpperField18X3 : highNormUpperX UpperResult18 3 = UpperField18Rows 3 := by decide +kernel
theorem UpperField18X4 : highNormUpperX UpperResult18 4 = UpperField18Rows 4 := by decide +kernel
theorem UpperField18X5 : highNormUpperX UpperResult18 5 = UpperField18Rows 5 := by decide +kernel
theorem UpperField18X6 : highNormUpperX UpperResult18 6 = UpperField18Rows 6 := by decide +kernel
theorem UpperField18X7 : highNormUpperX UpperResult18 7 = UpperField18Rows 7 := by decide +kernel
theorem UpperField18X8 : highNormUpperX UpperResult18 8 = UpperField18Rows 8 := by decide +kernel
theorem UpperField18X9 : highNormUpperX UpperResult18 9 = UpperField18Rows 9 := by decide +kernel
theorem UpperField18X10 : highNormUpperX UpperResult18 10 = UpperField18Rows 10 := by decide +kernel
theorem UpperField18X11 : highNormUpperX UpperResult18 11 = UpperField18Rows 11 := by decide +kernel
theorem UpperField18X12 : highNormUpperX UpperResult18 12 = UpperField18Rows 12 := by decide +kernel
theorem UpperField18X13 : highNormUpperX UpperResult18 13 = UpperField18Rows 13 := by decide +kernel
theorem UpperField18X14 : highNormUpperX UpperResult18 14 = UpperField18Rows 14 := by decide +kernel
theorem UpperField18X15 : highNormUpperX UpperResult18 15 = UpperField18Rows 15 := by decide +kernel
theorem UpperField18X16 : highNormUpperX UpperResult18 16 = UpperField18Rows 16 := by decide +kernel
theorem UpperField18X17 : highNormUpperX UpperResult18 17 = UpperField18Rows 17 := by decide +kernel
theorem UpperField18X18 : highNormUpperX UpperResult18 18 = UpperField18Rows 18 := by decide +kernel
theorem UpperField18X19 : highNormUpperX UpperResult18 19 = UpperField18Rows 19 := by decide +kernel
theorem UpperField18_rows (x : Fin 20) : highNormUpperX UpperResult18 x = UpperField18Rows x := by
  fin_cases x
  · exact UpperField18X0
  · exact UpperField18X1
  · exact UpperField18X2
  · exact UpperField18X3
  · exact UpperField18X4
  · exact UpperField18X5
  · exact UpperField18X6
  · exact UpperField18X7
  · exact UpperField18X8
  · exact UpperField18X9
  · exact UpperField18X10
  · exact UpperField18X11
  · exact UpperField18X12
  · exact UpperField18X13
  · exact UpperField18X14
  · exact UpperField18X15
  · exact UpperField18X16
  · exact UpperField18X17
  · exact UpperField18X18
  · exact UpperField18X19
theorem UpperField18_bound : highNormUpper UpperResult18 ≤ 96418195389310940437744601446435 :=
  highNormUpper_le_of_rows UpperResult18 UpperField18Rows 96418195389310940437744601446435 UpperField18_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
