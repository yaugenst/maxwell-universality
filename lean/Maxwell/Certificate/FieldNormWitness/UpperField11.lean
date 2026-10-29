import Maxwell.Certificate.ProjectionWitness.UpperResult11
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField11Rows : Fin 20 → ℤ := ![23796043680681079073638095188587, 19284600065253908334888395151829, 8810888221950168983495943138327, 744099948598321649820118455216, 271536987110651620394021973897, 114921718620272206738186124754, 46380633727172039916694952671, 23012099125991975231099755833, 15729582128272457590532394880, 4806989205367335329173613436, 4806989205367349945762508518, 15729582128272388204308201090, 23012099125992134542501223308, 46380633727172028782378577746, 114921718620273106086524560979, 271536987110648111584877740604, 744099948598327022493761759302, 8810888221950327657744307659456, 19284600065254057459222236649469, 23796043680681116921786053298805]
theorem UpperField11X0 : highNormUpperX UpperResult11 0 = UpperField11Rows 0 := by decide +kernel
theorem UpperField11X1 : highNormUpperX UpperResult11 1 = UpperField11Rows 1 := by decide +kernel
theorem UpperField11X2 : highNormUpperX UpperResult11 2 = UpperField11Rows 2 := by decide +kernel
theorem UpperField11X3 : highNormUpperX UpperResult11 3 = UpperField11Rows 3 := by decide +kernel
theorem UpperField11X4 : highNormUpperX UpperResult11 4 = UpperField11Rows 4 := by decide +kernel
theorem UpperField11X5 : highNormUpperX UpperResult11 5 = UpperField11Rows 5 := by decide +kernel
theorem UpperField11X6 : highNormUpperX UpperResult11 6 = UpperField11Rows 6 := by decide +kernel
theorem UpperField11X7 : highNormUpperX UpperResult11 7 = UpperField11Rows 7 := by decide +kernel
theorem UpperField11X8 : highNormUpperX UpperResult11 8 = UpperField11Rows 8 := by decide +kernel
theorem UpperField11X9 : highNormUpperX UpperResult11 9 = UpperField11Rows 9 := by decide +kernel
theorem UpperField11X10 : highNormUpperX UpperResult11 10 = UpperField11Rows 10 := by decide +kernel
theorem UpperField11X11 : highNormUpperX UpperResult11 11 = UpperField11Rows 11 := by decide +kernel
theorem UpperField11X12 : highNormUpperX UpperResult11 12 = UpperField11Rows 12 := by decide +kernel
theorem UpperField11X13 : highNormUpperX UpperResult11 13 = UpperField11Rows 13 := by decide +kernel
theorem UpperField11X14 : highNormUpperX UpperResult11 14 = UpperField11Rows 14 := by decide +kernel
theorem UpperField11X15 : highNormUpperX UpperResult11 15 = UpperField11Rows 15 := by decide +kernel
theorem UpperField11X16 : highNormUpperX UpperResult11 16 = UpperField11Rows 16 := by decide +kernel
theorem UpperField11X17 : highNormUpperX UpperResult11 17 = UpperField11Rows 17 := by decide +kernel
theorem UpperField11X18 : highNormUpperX UpperResult11 18 = UpperField11Rows 18 := by decide +kernel
theorem UpperField11X19 : highNormUpperX UpperResult11 19 = UpperField11Rows 19 := by decide +kernel
theorem UpperField11_rows (x : Fin 20) : highNormUpperX UpperResult11 x = UpperField11Rows x := by
  fin_cases x
  · exact UpperField11X0
  · exact UpperField11X1
  · exact UpperField11X2
  · exact UpperField11X3
  · exact UpperField11X4
  · exact UpperField11X5
  · exact UpperField11X6
  · exact UpperField11X7
  · exact UpperField11X8
  · exact UpperField11X9
  · exact UpperField11X10
  · exact UpperField11X11
  · exact UpperField11X12
  · exact UpperField11X13
  · exact UpperField11X14
  · exact UpperField11X15
  · exact UpperField11X16
  · exact UpperField11X17
  · exact UpperField11X18
  · exact UpperField11X19
theorem UpperField11_bound : highNormUpper UpperResult11 ≤ 106224039852802759857434972928707 :=
  highNormUpper_le_of_rows UpperResult11 UpperField11Rows 106224039852802759857434972928707 UpperField11_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
