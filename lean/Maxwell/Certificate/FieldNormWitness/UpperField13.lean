import Maxwell.Certificate.ProjectionWitness.UpperResult13
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField13Rows : Fin 20 → ℤ := ![25544535156378635136626832966321, 8195024348278943799880900825633, 4735676116978445280780403432009, 227318429210190665042394443296, 165455828153793816595014498419, 46104488676512039848551777650, 19992221131490620272045146645, 14793582630554242537194245164, 7151900252828899122532888580, 6203627176859896522906534668, 6203627176859951828735491184, 7151900252828829594692411545, 14793582630554645584391262514, 19992221131490272672397884275, 46104488676512536763367450045, 165455828153796015732597180260, 227318429210189910857998044226, 4735676116978434135896725076040, 8195024348278989842137714548757, 25544535156378585081572843592581]
theorem UpperField13X0 : highNormUpperX UpperResult13 0 = UpperField13Rows 0 := by decide +kernel
theorem UpperField13X1 : highNormUpperX UpperResult13 1 = UpperField13Rows 1 := by decide +kernel
theorem UpperField13X2 : highNormUpperX UpperResult13 2 = UpperField13Rows 2 := by decide +kernel
theorem UpperField13X3 : highNormUpperX UpperResult13 3 = UpperField13Rows 3 := by decide +kernel
theorem UpperField13X4 : highNormUpperX UpperResult13 4 = UpperField13Rows 4 := by decide +kernel
theorem UpperField13X5 : highNormUpperX UpperResult13 5 = UpperField13Rows 5 := by decide +kernel
theorem UpperField13X6 : highNormUpperX UpperResult13 6 = UpperField13Rows 6 := by decide +kernel
theorem UpperField13X7 : highNormUpperX UpperResult13 7 = UpperField13Rows 7 := by decide +kernel
theorem UpperField13X8 : highNormUpperX UpperResult13 8 = UpperField13Rows 8 := by decide +kernel
theorem UpperField13X9 : highNormUpperX UpperResult13 9 = UpperField13Rows 9 := by decide +kernel
theorem UpperField13X10 : highNormUpperX UpperResult13 10 = UpperField13Rows 10 := by decide +kernel
theorem UpperField13X11 : highNormUpperX UpperResult13 11 = UpperField13Rows 11 := by decide +kernel
theorem UpperField13X12 : highNormUpperX UpperResult13 12 = UpperField13Rows 12 := by decide +kernel
theorem UpperField13X13 : highNormUpperX UpperResult13 13 = UpperField13Rows 13 := by decide +kernel
theorem UpperField13X14 : highNormUpperX UpperResult13 14 = UpperField13Rows 14 := by decide +kernel
theorem UpperField13X15 : highNormUpperX UpperResult13 15 = UpperField13Rows 15 := by decide +kernel
theorem UpperField13X16 : highNormUpperX UpperResult13 16 = UpperField13Rows 16 := by decide +kernel
theorem UpperField13X17 : highNormUpperX UpperResult13 17 = UpperField13Rows 17 := by decide +kernel
theorem UpperField13X18 : highNormUpperX UpperResult13 18 = UpperField13Rows 18 := by decide +kernel
theorem UpperField13X19 : highNormUpperX UpperResult13 19 = UpperField13Rows 19 := by decide +kernel
theorem UpperField13_rows (x : Fin 20) : highNormUpperX UpperResult13 x = UpperField13Rows x := by
  fin_cases x
  · exact UpperField13X0
  · exact UpperField13X1
  · exact UpperField13X2
  · exact UpperField13X3
  · exact UpperField13X4
  · exact UpperField13X5
  · exact UpperField13X6
  · exact UpperField13X7
  · exact UpperField13X8
  · exact UpperField13X9
  · exact UpperField13X10
  · exact UpperField13X11
  · exact UpperField13X12
  · exact UpperField13X13
  · exact UpperField13X14
  · exact UpperField13X15
  · exact UpperField13X16
  · exact UpperField13X17
  · exact UpperField13X18
  · exact UpperField13X19
theorem UpperField13_bound : highNormUpper UpperResult13 ≤ 77924511397736495619870239699812 :=
  highNormUpper_le_of_rows UpperResult13 UpperField13Rows 77924511397736495619870239699812 UpperField13_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
