import Maxwell.Certificate.ProjectionWitness.UpperResult3
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField03Rows : Fin 20 → ℤ := ![13042056031363366273779898245309, 88873014221739208372807905309968, 19747345042497958777818418489237, 2547963171104269041694406208770, 1718238944177818149699885182934, 239332567529793255318982862901, 299458164933893832309074743623, 63577094549509520493032308216, 75254800945881096785229674268, 20835032392296901663662935136, 20835032392296193136872525951, 75254800945879794433708524788, 63577094549508370138824787222, 299458164933896067783453654450, 239332567529793488083582526563, 1718238944177807109234640881465, 2547963171104273827472989404326, 19747345042497902809282706801608, 88873014221740050184563214277312, 13042056031363414731902876401145]
theorem UpperField03X0 : highNormUpperX UpperResult3 0 = UpperField03Rows 0 := by decide +kernel
theorem UpperField03X1 : highNormUpperX UpperResult3 1 = UpperField03Rows 1 := by decide +kernel
theorem UpperField03X2 : highNormUpperX UpperResult3 2 = UpperField03Rows 2 := by decide +kernel
theorem UpperField03X3 : highNormUpperX UpperResult3 3 = UpperField03Rows 3 := by decide +kernel
theorem UpperField03X4 : highNormUpperX UpperResult3 4 = UpperField03Rows 4 := by decide +kernel
theorem UpperField03X5 : highNormUpperX UpperResult3 5 = UpperField03Rows 5 := by decide +kernel
theorem UpperField03X6 : highNormUpperX UpperResult3 6 = UpperField03Rows 6 := by decide +kernel
theorem UpperField03X7 : highNormUpperX UpperResult3 7 = UpperField03Rows 7 := by decide +kernel
theorem UpperField03X8 : highNormUpperX UpperResult3 8 = UpperField03Rows 8 := by decide +kernel
theorem UpperField03X9 : highNormUpperX UpperResult3 9 = UpperField03Rows 9 := by decide +kernel
theorem UpperField03X10 : highNormUpperX UpperResult3 10 = UpperField03Rows 10 := by decide +kernel
theorem UpperField03X11 : highNormUpperX UpperResult3 11 = UpperField03Rows 11 := by decide +kernel
theorem UpperField03X12 : highNormUpperX UpperResult3 12 = UpperField03Rows 12 := by decide +kernel
theorem UpperField03X13 : highNormUpperX UpperResult3 13 = UpperField03Rows 13 := by decide +kernel
theorem UpperField03X14 : highNormUpperX UpperResult3 14 = UpperField03Rows 14 := by decide +kernel
theorem UpperField03X15 : highNormUpperX UpperResult3 15 = UpperField03Rows 15 := by decide +kernel
theorem UpperField03X16 : highNormUpperX UpperResult3 16 = UpperField03Rows 16 := by decide +kernel
theorem UpperField03X17 : highNormUpperX UpperResult3 17 = UpperField03Rows 17 := by decide +kernel
theorem UpperField03X18 : highNormUpperX UpperResult3 18 = UpperField03Rows 18 := by decide +kernel
theorem UpperField03X19 : highNormUpperX UpperResult3 19 = UpperField03Rows 19 := by decide +kernel
theorem UpperField03_rows (x : Fin 20) : highNormUpperX UpperResult3 x = UpperField03Rows x := by
  fin_cases x
  · exact UpperField03X0
  · exact UpperField03X1
  · exact UpperField03X2
  · exact UpperField03X3
  · exact UpperField03X4
  · exact UpperField03X5
  · exact UpperField03X6
  · exact UpperField03X7
  · exact UpperField03X8
  · exact UpperField03X9
  · exact UpperField03X10
  · exact UpperField03X11
  · exact UpperField03X12
  · exact UpperField03X13
  · exact UpperField03X14
  · exact UpperField03X15
  · exact UpperField03X16
  · exact UpperField03X17
  · exact UpperField03X18
  · exact UpperField03X19
theorem UpperField03_bound : highNormUpper UpperResult3 ≤ 253254150142468817798403365745192 :=
  highNormUpper_le_of_rows UpperResult3 UpperField03Rows 253254150142468817798403365745192 UpperField03_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
