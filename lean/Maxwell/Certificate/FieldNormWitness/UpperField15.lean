import Maxwell.Certificate.ProjectionWitness.UpperResult15
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField15Rows : Fin 20 → ℤ := ![10802210634180869622501146201104, 12423219484051368083381038228271, 13742061060337473404882364530244, 965308883043332917442024521319, 319278659053894633480954615713, 124358234854557766118345655996, 52311450343636074860964631285, 25410069410599919816196789197, 13274896365352137093141898466, 7956415786518950485090956246, 7956415786519226851430101982, 13274896365352036225538868942, 25410069410599738020352789418, 52311450343636412474423479209, 124358234854559771129045932701, 319278659053896145108128073746, 965308883043336389726840186128, 13742061060337610472376978895442, 12423219484051377145924894825085, 10802210634180950190513152975519]
theorem UpperField15X0 : highNormUpperX UpperResult15 0 = UpperField15Rows 0 := by decide +kernel
theorem UpperField15X1 : highNormUpperX UpperResult15 1 = UpperField15Rows 1 := by decide +kernel
theorem UpperField15X2 : highNormUpperX UpperResult15 2 = UpperField15Rows 2 := by decide +kernel
theorem UpperField15X3 : highNormUpperX UpperResult15 3 = UpperField15Rows 3 := by decide +kernel
theorem UpperField15X4 : highNormUpperX UpperResult15 4 = UpperField15Rows 4 := by decide +kernel
theorem UpperField15X5 : highNormUpperX UpperResult15 5 = UpperField15Rows 5 := by decide +kernel
theorem UpperField15X6 : highNormUpperX UpperResult15 6 = UpperField15Rows 6 := by decide +kernel
theorem UpperField15X7 : highNormUpperX UpperResult15 7 = UpperField15Rows 7 := by decide +kernel
theorem UpperField15X8 : highNormUpperX UpperResult15 8 = UpperField15Rows 8 := by decide +kernel
theorem UpperField15X9 : highNormUpperX UpperResult15 9 = UpperField15Rows 9 := by decide +kernel
theorem UpperField15X10 : highNormUpperX UpperResult15 10 = UpperField15Rows 10 := by decide +kernel
theorem UpperField15X11 : highNormUpperX UpperResult15 11 = UpperField15Rows 11 := by decide +kernel
theorem UpperField15X12 : highNormUpperX UpperResult15 12 = UpperField15Rows 12 := by decide +kernel
theorem UpperField15X13 : highNormUpperX UpperResult15 13 = UpperField15Rows 13 := by decide +kernel
theorem UpperField15X14 : highNormUpperX UpperResult15 14 = UpperField15Rows 14 := by decide +kernel
theorem UpperField15X15 : highNormUpperX UpperResult15 15 = UpperField15Rows 15 := by decide +kernel
theorem UpperField15X16 : highNormUpperX UpperResult15 16 = UpperField15Rows 16 := by decide +kernel
theorem UpperField15X17 : highNormUpperX UpperResult15 17 = UpperField15Rows 17 := by decide +kernel
theorem UpperField15X18 : highNormUpperX UpperResult15 18 = UpperField15Rows 18 := by decide +kernel
theorem UpperField15X19 : highNormUpperX UpperResult15 19 = UpperField15Rows 19 := by decide +kernel
theorem UpperField15_rows (x : Fin 20) : highNormUpperX UpperResult15 x = UpperField15Rows x := by
  fin_cases x
  · exact UpperField15X0
  · exact UpperField15X1
  · exact UpperField15X2
  · exact UpperField15X3
  · exact UpperField15X4
  · exact UpperField15X5
  · exact UpperField15X6
  · exact UpperField15X7
  · exact UpperField15X8
  · exact UpperField15X9
  · exact UpperField15X10
  · exact UpperField15X11
  · exact UpperField15X12
  · exact UpperField15X13
  · exact UpperField15X14
  · exact UpperField15X15
  · exact UpperField15X16
  · exact UpperField15X17
  · exact UpperField15X18
  · exact UpperField15X19
theorem UpperField15_bound : highNormUpper UpperResult15 ≤ 76950779574855441038412054156013 :=
  highNormUpper_le_of_rows UpperResult15 UpperField15Rows 76950779574855441038412054156013 UpperField15_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
