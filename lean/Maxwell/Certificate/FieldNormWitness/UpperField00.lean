import Maxwell.Certificate.ProjectionWitness.UpperResult0
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField00Rows : Fin 20 → ℤ := ![1960907594570065305179238456439, 7964398701645434220780568132085, 2986806540726966568072601044451, 814497999555774683914335313742, 167498729684175005849502235929, 81797677336313502754737198180, 26127701648891711929500553836, 10956040848982155237896293643, 4653074670250143590862501974, 720615836957040415445608262, 720615836957115840510447229, 4653074670250166173560257716, 10956040848982072196798565211, 26127701648891373795298087253, 81797677336313472479363471718, 167498729684175470878575200653, 814497999555771190875989213243, 2986806540726951964626563984699, 7964398701645468726217393990453, 1960907594570051800390789583873]
theorem UpperField00X0 : highNormUpperX UpperResult0 0 = UpperField00Rows 0 := by decide +kernel
theorem UpperField00X1 : highNormUpperX UpperResult0 1 = UpperField00Rows 1 := by decide +kernel
theorem UpperField00X2 : highNormUpperX UpperResult0 2 = UpperField00Rows 2 := by decide +kernel
theorem UpperField00X3 : highNormUpperX UpperResult0 3 = UpperField00Rows 3 := by decide +kernel
theorem UpperField00X4 : highNormUpperX UpperResult0 4 = UpperField00Rows 4 := by decide +kernel
theorem UpperField00X5 : highNormUpperX UpperResult0 5 = UpperField00Rows 5 := by decide +kernel
theorem UpperField00X6 : highNormUpperX UpperResult0 6 = UpperField00Rows 6 := by decide +kernel
theorem UpperField00X7 : highNormUpperX UpperResult0 7 = UpperField00Rows 7 := by decide +kernel
theorem UpperField00X8 : highNormUpperX UpperResult0 8 = UpperField00Rows 8 := by decide +kernel
theorem UpperField00X9 : highNormUpperX UpperResult0 9 = UpperField00Rows 9 := by decide +kernel
theorem UpperField00X10 : highNormUpperX UpperResult0 10 = UpperField00Rows 10 := by decide +kernel
theorem UpperField00X11 : highNormUpperX UpperResult0 11 = UpperField00Rows 11 := by decide +kernel
theorem UpperField00X12 : highNormUpperX UpperResult0 12 = UpperField00Rows 12 := by decide +kernel
theorem UpperField00X13 : highNormUpperX UpperResult0 13 = UpperField00Rows 13 := by decide +kernel
theorem UpperField00X14 : highNormUpperX UpperResult0 14 = UpperField00Rows 14 := by decide +kernel
theorem UpperField00X15 : highNormUpperX UpperResult0 15 = UpperField00Rows 15 := by decide +kernel
theorem UpperField00X16 : highNormUpperX UpperResult0 16 = UpperField00Rows 16 := by decide +kernel
theorem UpperField00X17 : highNormUpperX UpperResult0 17 = UpperField00Rows 17 := by decide +kernel
theorem UpperField00X18 : highNormUpperX UpperResult0 18 = UpperField00Rows 18 := by decide +kernel
theorem UpperField00X19 : highNormUpperX UpperResult0 19 = UpperField00Rows 19 := by decide +kernel
theorem UpperField00_rows (x : Fin 20) : highNormUpperX UpperResult0 x = UpperField00Rows x := by
  fin_cases x
  · exact UpperField00X0
  · exact UpperField00X1
  · exact UpperField00X2
  · exact UpperField00X3
  · exact UpperField00X4
  · exact UpperField00X5
  · exact UpperField00X6
  · exact UpperField00X7
  · exact UpperField00X8
  · exact UpperField00X9
  · exact UpperField00X10
  · exact UpperField00X11
  · exact UpperField00X12
  · exact UpperField00X13
  · exact UpperField00X14
  · exact UpperField00X15
  · exact UpperField00X16
  · exact UpperField00X17
  · exact UpperField00X18
  · exact UpperField00X19
theorem UpperField00_bound : highNormUpper UpperResult0 ≤ 28036729353047623691199530140589 :=
  highNormUpper_le_of_rows UpperResult0 UpperField00Rows 28036729353047623691199530140589 UpperField00_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
