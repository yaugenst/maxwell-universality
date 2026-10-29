import Maxwell.Certificate.ProjectionWitness.UpperResult2
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField02Rows : Fin 20 → ℤ := ![25688790662579998948197731030024, 81584001136584960909546271012590, 14443472535133908109266570068009, 2701177174224578308588905790041, 1649893144534651519024939219966, 215475762874489449508309926276, 260091795408702224619200925823, 37402018382999102160123397729, 40539729423543702833388003767, 6231112085851405278043038553, 6231112085850935145833405000, 40539729423544082882768844078, 37402018382998939697553610286, 260091795408702779312568064424, 215475762874486712459458245562, 1649893144534648900571436414872, 2701177174224580079670395901435, 14443472535134040801652897371328, 81584001136585346495395858351941, 25688790662579991953890991698590]
theorem UpperField02X0 : highNormUpperX UpperResult2 0 = UpperField02Rows 0 := by decide +kernel
theorem UpperField02X1 : highNormUpperX UpperResult2 1 = UpperField02Rows 1 := by decide +kernel
theorem UpperField02X2 : highNormUpperX UpperResult2 2 = UpperField02Rows 2 := by decide +kernel
theorem UpperField02X3 : highNormUpperX UpperResult2 3 = UpperField02Rows 3 := by decide +kernel
theorem UpperField02X4 : highNormUpperX UpperResult2 4 = UpperField02Rows 4 := by decide +kernel
theorem UpperField02X5 : highNormUpperX UpperResult2 5 = UpperField02Rows 5 := by decide +kernel
theorem UpperField02X6 : highNormUpperX UpperResult2 6 = UpperField02Rows 6 := by decide +kernel
theorem UpperField02X7 : highNormUpperX UpperResult2 7 = UpperField02Rows 7 := by decide +kernel
theorem UpperField02X8 : highNormUpperX UpperResult2 8 = UpperField02Rows 8 := by decide +kernel
theorem UpperField02X9 : highNormUpperX UpperResult2 9 = UpperField02Rows 9 := by decide +kernel
theorem UpperField02X10 : highNormUpperX UpperResult2 10 = UpperField02Rows 10 := by decide +kernel
theorem UpperField02X11 : highNormUpperX UpperResult2 11 = UpperField02Rows 11 := by decide +kernel
theorem UpperField02X12 : highNormUpperX UpperResult2 12 = UpperField02Rows 12 := by decide +kernel
theorem UpperField02X13 : highNormUpperX UpperResult2 13 = UpperField02Rows 13 := by decide +kernel
theorem UpperField02X14 : highNormUpperX UpperResult2 14 = UpperField02Rows 14 := by decide +kernel
theorem UpperField02X15 : highNormUpperX UpperResult2 15 = UpperField02Rows 15 := by decide +kernel
theorem UpperField02X16 : highNormUpperX UpperResult2 16 = UpperField02Rows 16 := by decide +kernel
theorem UpperField02X17 : highNormUpperX UpperResult2 17 = UpperField02Rows 17 := by decide +kernel
theorem UpperField02X18 : highNormUpperX UpperResult2 18 = UpperField02Rows 18 := by decide +kernel
theorem UpperField02X19 : highNormUpperX UpperResult2 19 = UpperField02Rows 19 := by decide +kernel
theorem UpperField02_rows (x : Fin 20) : highNormUpperX UpperResult2 x = UpperField02Rows x := by
  fin_cases x
  · exact UpperField02X0
  · exact UpperField02X1
  · exact UpperField02X2
  · exact UpperField02X3
  · exact UpperField02X4
  · exact UpperField02X5
  · exact UpperField02X6
  · exact UpperField02X7
  · exact UpperField02X8
  · exact UpperField02X9
  · exact UpperField02X10
  · exact UpperField02X11
  · exact UpperField02X12
  · exact UpperField02X13
  · exact UpperField02X14
  · exact UpperField02X15
  · exact UpperField02X16
  · exact UpperField02X17
  · exact UpperField02X18
  · exact UpperField02X19
theorem UpperField02_bound : highNormUpper UpperResult2 ≤ 253254150142467875359703244320294 :=
  highNormUpper_le_of_rows UpperResult2 UpperField02Rows 253254150142467875359703244320294 UpperField02_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
