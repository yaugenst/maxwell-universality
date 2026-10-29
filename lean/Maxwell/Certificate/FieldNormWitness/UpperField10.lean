import Maxwell.Certificate.ProjectionWitness.UpperResult10
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField10Rows : Fin 20 → ℤ := ![13747475554797354568281842869064, 16201583550454824842934932751720, 16602197849808514796105934002206, 579434950718686376561674013857, 537353792674493313768472248925, 79550351523710184492727860552, 70207267099614953076653188625, 18075395946537359606066243396, 12399199540463091579205829316, 4068355199096231403330413592, 4068355199096182005690968607, 12399199540463253026123695436, 18075395946536938602534242716, 70207267099615834023769311670, 79550351523709509629935156420, 537353792674492040905050117834, 579434950718691826008998488734, 16602197849808366402899101600981, 16201583550454796197036045052380, 13747475554797321014952793367208]
theorem UpperField10X0 : highNormUpperX UpperResult10 0 = UpperField10Rows 0 := by decide +kernel
theorem UpperField10X1 : highNormUpperX UpperResult10 1 = UpperField10Rows 1 := by decide +kernel
theorem UpperField10X2 : highNormUpperX UpperResult10 2 = UpperField10Rows 2 := by decide +kernel
theorem UpperField10X3 : highNormUpperX UpperResult10 3 = UpperField10Rows 3 := by decide +kernel
theorem UpperField10X4 : highNormUpperX UpperResult10 4 = UpperField10Rows 4 := by decide +kernel
theorem UpperField10X5 : highNormUpperX UpperResult10 5 = UpperField10Rows 5 := by decide +kernel
theorem UpperField10X6 : highNormUpperX UpperResult10 6 = UpperField10Rows 6 := by decide +kernel
theorem UpperField10X7 : highNormUpperX UpperResult10 7 = UpperField10Rows 7 := by decide +kernel
theorem UpperField10X8 : highNormUpperX UpperResult10 8 = UpperField10Rows 8 := by decide +kernel
theorem UpperField10X9 : highNormUpperX UpperResult10 9 = UpperField10Rows 9 := by decide +kernel
theorem UpperField10X10 : highNormUpperX UpperResult10 10 = UpperField10Rows 10 := by decide +kernel
theorem UpperField10X11 : highNormUpperX UpperResult10 11 = UpperField10Rows 11 := by decide +kernel
theorem UpperField10X12 : highNormUpperX UpperResult10 12 = UpperField10Rows 12 := by decide +kernel
theorem UpperField10X13 : highNormUpperX UpperResult10 13 = UpperField10Rows 13 := by decide +kernel
theorem UpperField10X14 : highNormUpperX UpperResult10 14 = UpperField10Rows 14 := by decide +kernel
theorem UpperField10X15 : highNormUpperX UpperResult10 15 = UpperField10Rows 15 := by decide +kernel
theorem UpperField10X16 : highNormUpperX UpperResult10 16 = UpperField10Rows 16 := by decide +kernel
theorem UpperField10X17 : highNormUpperX UpperResult10 17 = UpperField10Rows 17 := by decide +kernel
theorem UpperField10X18 : highNormUpperX UpperResult10 18 = UpperField10Rows 18 := by decide +kernel
theorem UpperField10X19 : highNormUpperX UpperResult10 19 = UpperField10Rows 19 := by decide +kernel
theorem UpperField10_rows (x : Fin 20) : highNormUpperX UpperResult10 x = UpperField10Rows x := by
  fin_cases x
  · exact UpperField10X0
  · exact UpperField10X1
  · exact UpperField10X2
  · exact UpperField10X3
  · exact UpperField10X4
  · exact UpperField10X5
  · exact UpperField10X6
  · exact UpperField10X7
  · exact UpperField10X8
  · exact UpperField10X9
  · exact UpperField10X10
  · exact UpperField10X11
  · exact UpperField10X12
  · exact UpperField10X13
  · exact UpperField10X14
  · exact UpperField10X15
  · exact UpperField10X16
  · exact UpperField10X17
  · exact UpperField10X18
  · exact UpperField10X19
theorem UpperField10_bound : highNormUpper UpperResult10 ≤ 95704692535526384916900881423239 :=
  highNormUpper_le_of_rows UpperResult10 UpperField10Rows 95704692535526384916900881423239 UpperField10_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
