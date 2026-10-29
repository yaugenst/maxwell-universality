import Maxwell.Certificate.AppliedWitness.UpperApplied3
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied03Rows : Fin 20 → ℤ := ![15628763699104, 86712986618516, 98971364715929, 115837350157131, 136245112445193, 31491816892677, 164535521876811, 166536960474137, 164142866547470, 158056970102490, 32915089708377, 169760508871831, 168215137845822, 162487773477610, 153008535725668, 28036553556235, 117193854785257, 97685070101868, 83273497636555, 74806264585800]
theorem UpperApplied03X0 : highNormUpperX UpperApplied3 0 = UpperApplied03Rows 0 := by decide +kernel
theorem UpperApplied03X1 : highNormUpperX UpperApplied3 1 = UpperApplied03Rows 1 := by decide +kernel
theorem UpperApplied03X2 : highNormUpperX UpperApplied3 2 = UpperApplied03Rows 2 := by decide +kernel
theorem UpperApplied03X3 : highNormUpperX UpperApplied3 3 = UpperApplied03Rows 3 := by decide +kernel
theorem UpperApplied03X4 : highNormUpperX UpperApplied3 4 = UpperApplied03Rows 4 := by decide +kernel
theorem UpperApplied03X5 : highNormUpperX UpperApplied3 5 = UpperApplied03Rows 5 := by decide +kernel
theorem UpperApplied03X6 : highNormUpperX UpperApplied3 6 = UpperApplied03Rows 6 := by decide +kernel
theorem UpperApplied03X7 : highNormUpperX UpperApplied3 7 = UpperApplied03Rows 7 := by decide +kernel
theorem UpperApplied03X8 : highNormUpperX UpperApplied3 8 = UpperApplied03Rows 8 := by decide +kernel
theorem UpperApplied03X9 : highNormUpperX UpperApplied3 9 = UpperApplied03Rows 9 := by decide +kernel
theorem UpperApplied03X10 : highNormUpperX UpperApplied3 10 = UpperApplied03Rows 10 := by decide +kernel
theorem UpperApplied03X11 : highNormUpperX UpperApplied3 11 = UpperApplied03Rows 11 := by decide +kernel
theorem UpperApplied03X12 : highNormUpperX UpperApplied3 12 = UpperApplied03Rows 12 := by decide +kernel
theorem UpperApplied03X13 : highNormUpperX UpperApplied3 13 = UpperApplied03Rows 13 := by decide +kernel
theorem UpperApplied03X14 : highNormUpperX UpperApplied3 14 = UpperApplied03Rows 14 := by decide +kernel
theorem UpperApplied03X15 : highNormUpperX UpperApplied3 15 = UpperApplied03Rows 15 := by decide +kernel
theorem UpperApplied03X16 : highNormUpperX UpperApplied3 16 = UpperApplied03Rows 16 := by decide +kernel
theorem UpperApplied03X17 : highNormUpperX UpperApplied3 17 = UpperApplied03Rows 17 := by decide +kernel
theorem UpperApplied03X18 : highNormUpperX UpperApplied3 18 = UpperApplied03Rows 18 := by decide +kernel
theorem UpperApplied03X19 : highNormUpperX UpperApplied3 19 = UpperApplied03Rows 19 := by decide +kernel
theorem UpperApplied03_rows (x : Fin 20) : highNormUpperX UpperApplied3 x = UpperApplied03Rows x := by
  fin_cases x
  · exact UpperApplied03X0
  · exact UpperApplied03X1
  · exact UpperApplied03X2
  · exact UpperApplied03X3
  · exact UpperApplied03X4
  · exact UpperApplied03X5
  · exact UpperApplied03X6
  · exact UpperApplied03X7
  · exact UpperApplied03X8
  · exact UpperApplied03X9
  · exact UpperApplied03X10
  · exact UpperApplied03X11
  · exact UpperApplied03X12
  · exact UpperApplied03X13
  · exact UpperApplied03X14
  · exact UpperApplied03X15
  · exact UpperApplied03X16
  · exact UpperApplied03X17
  · exact UpperApplied03X18
  · exact UpperApplied03X19
theorem UpperApplied03_bound : highNormUpper UpperApplied3 ≤ 2225541999824481 :=
  highNormUpper_le_of_rows UpperApplied3 UpperApplied03Rows 2225541999824481 UpperApplied03_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
