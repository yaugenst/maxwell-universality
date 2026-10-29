import Maxwell.Certificate.ProjectionWitness.UpperResult1
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField01Rows : Fin 20 → ℤ := ![4746189458959186420145718853677, 8191345787828420983454542209500, 628101493949965195635917485220, 332159037508752242605232349661, 46798271124582205318832304422, 43204643041134540583506512204, 8934952964680451343543701333, 13933423963794304230640852305, 4722306799728243225476064003, 2975300383680760474187273445, 2975300383680551309861522276, 4722306799728025375397957506, 13933423963794030940332313044, 8934952964680176031974156215, 43204643041134713341008436654, 46798271124581570358500061117, 332159037508748272847630485932, 628101493949958577726830153706, 8191345787828298628289038408492, 4746189458959167277121604175079]
theorem UpperField01X0 : highNormUpperX UpperResult1 0 = UpperField01Rows 0 := by decide +kernel
theorem UpperField01X1 : highNormUpperX UpperResult1 1 = UpperField01Rows 1 := by decide +kernel
theorem UpperField01X2 : highNormUpperX UpperResult1 2 = UpperField01Rows 2 := by decide +kernel
theorem UpperField01X3 : highNormUpperX UpperResult1 3 = UpperField01Rows 3 := by decide +kernel
theorem UpperField01X4 : highNormUpperX UpperResult1 4 = UpperField01Rows 4 := by decide +kernel
theorem UpperField01X5 : highNormUpperX UpperResult1 5 = UpperField01Rows 5 := by decide +kernel
theorem UpperField01X6 : highNormUpperX UpperResult1 6 = UpperField01Rows 6 := by decide +kernel
theorem UpperField01X7 : highNormUpperX UpperResult1 7 = UpperField01Rows 7 := by decide +kernel
theorem UpperField01X8 : highNormUpperX UpperResult1 8 = UpperField01Rows 8 := by decide +kernel
theorem UpperField01X9 : highNormUpperX UpperResult1 9 = UpperField01Rows 9 := by decide +kernel
theorem UpperField01X10 : highNormUpperX UpperResult1 10 = UpperField01Rows 10 := by decide +kernel
theorem UpperField01X11 : highNormUpperX UpperResult1 11 = UpperField01Rows 11 := by decide +kernel
theorem UpperField01X12 : highNormUpperX UpperResult1 12 = UpperField01Rows 12 := by decide +kernel
theorem UpperField01X13 : highNormUpperX UpperResult1 13 = UpperField01Rows 13 := by decide +kernel
theorem UpperField01X14 : highNormUpperX UpperResult1 14 = UpperField01Rows 14 := by decide +kernel
theorem UpperField01X15 : highNormUpperX UpperResult1 15 = UpperField01Rows 15 := by decide +kernel
theorem UpperField01X16 : highNormUpperX UpperResult1 16 = UpperField01Rows 16 := by decide +kernel
theorem UpperField01X17 : highNormUpperX UpperResult1 17 = UpperField01Rows 17 := by decide +kernel
theorem UpperField01X18 : highNormUpperX UpperResult1 18 = UpperField01Rows 18 := by decide +kernel
theorem UpperField01X19 : highNormUpperX UpperResult1 19 = UpperField01Rows 19 := by decide +kernel
theorem UpperField01_rows (x : Fin 20) : highNormUpperX UpperResult1 x = UpperField01Rows x := by
  fin_cases x
  · exact UpperField01X0
  · exact UpperField01X1
  · exact UpperField01X2
  · exact UpperField01X3
  · exact UpperField01X4
  · exact UpperField01X5
  · exact UpperField01X6
  · exact UpperField01X7
  · exact UpperField01X8
  · exact UpperField01X9
  · exact UpperField01X10
  · exact UpperField01X11
  · exact UpperField01X12
  · exact UpperField01X13
  · exact UpperField01X14
  · exact UpperField01X15
  · exact UpperField01X16
  · exact UpperField01X17
  · exact UpperField01X18
  · exact UpperField01X19
theorem UpperField01_bound : highNormUpper UpperResult1 ≤ 28036729353047697170359775275791 :=
  highNormUpper_le_of_rows UpperResult1 UpperField01Rows 28036729353047697170359775275791 UpperField01_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
