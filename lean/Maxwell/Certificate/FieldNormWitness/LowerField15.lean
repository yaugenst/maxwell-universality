import Maxwell.Certificate.ProjectionWitness.LowerResult15
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField15Rows : Fin 20 → ℤ := ![18615508895005383980709731599283, 11472678019801164176787160846709, 20229245931395861042271939069696, 1575924691064865724203971467595, 330599415748950370349201783675, 275208775783139683469762653039, 36154146277323530787287531972, 50308617903651479590688431692, 8491456948205858546273010034, 14173547206733835386189523370, 14173547206734125105522676289, 8491456948206093059311519806, 50308617903651006589846016584, 36154146277324782930702725164, 275208775783139464556937030129, 330599415748950449934030997299, 1575924691064861077170895134565, 20229245931395822702819226137263, 11472678019801090580877490568006, 18615508895005426684567455033387]
theorem LowerField15X0 : highNormUpperX LowerResult15 0 = LowerField15Rows 0 := by decide +kernel
theorem LowerField15X1 : highNormUpperX LowerResult15 1 = LowerField15Rows 1 := by decide +kernel
theorem LowerField15X2 : highNormUpperX LowerResult15 2 = LowerField15Rows 2 := by decide +kernel
theorem LowerField15X3 : highNormUpperX LowerResult15 3 = LowerField15Rows 3 := by decide +kernel
theorem LowerField15X4 : highNormUpperX LowerResult15 4 = LowerField15Rows 4 := by decide +kernel
theorem LowerField15X5 : highNormUpperX LowerResult15 5 = LowerField15Rows 5 := by decide +kernel
theorem LowerField15X6 : highNormUpperX LowerResult15 6 = LowerField15Rows 6 := by decide +kernel
theorem LowerField15X7 : highNormUpperX LowerResult15 7 = LowerField15Rows 7 := by decide +kernel
theorem LowerField15X8 : highNormUpperX LowerResult15 8 = LowerField15Rows 8 := by decide +kernel
theorem LowerField15X9 : highNormUpperX LowerResult15 9 = LowerField15Rows 9 := by decide +kernel
theorem LowerField15X10 : highNormUpperX LowerResult15 10 = LowerField15Rows 10 := by decide +kernel
theorem LowerField15X11 : highNormUpperX LowerResult15 11 = LowerField15Rows 11 := by decide +kernel
theorem LowerField15X12 : highNormUpperX LowerResult15 12 = LowerField15Rows 12 := by decide +kernel
theorem LowerField15X13 : highNormUpperX LowerResult15 13 = LowerField15Rows 13 := by decide +kernel
theorem LowerField15X14 : highNormUpperX LowerResult15 14 = LowerField15Rows 14 := by decide +kernel
theorem LowerField15X15 : highNormUpperX LowerResult15 15 = LowerField15Rows 15 := by decide +kernel
theorem LowerField15X16 : highNormUpperX LowerResult15 16 = LowerField15Rows 16 := by decide +kernel
theorem LowerField15X17 : highNormUpperX LowerResult15 17 = LowerField15Rows 17 := by decide +kernel
theorem LowerField15X18 : highNormUpperX LowerResult15 18 = LowerField15Rows 18 := by decide +kernel
theorem LowerField15X19 : highNormUpperX LowerResult15 19 = LowerField15Rows 19 := by decide +kernel
theorem LowerField15_rows (x : Fin 20) : highNormUpperX LowerResult15 x = LowerField15Rows x := by
  fin_cases x
  · exact LowerField15X0
  · exact LowerField15X1
  · exact LowerField15X2
  · exact LowerField15X3
  · exact LowerField15X4
  · exact LowerField15X5
  · exact LowerField15X6
  · exact LowerField15X7
  · exact LowerField15X8
  · exact LowerField15X9
  · exact LowerField15X10
  · exact LowerField15X11
  · exact LowerField15X12
  · exact LowerField15X13
  · exact LowerField15X14
  · exact LowerField15X15
  · exact LowerField15X16
  · exact LowerField15X17
  · exact LowerField15X18
  · exact LowerField15X19
theorem LowerField15_bound : highNormUpper LowerResult15 ≤ 105216586994270486649713623755557 :=
  highNormUpper_le_of_rows LowerResult15 LowerField15Rows 105216586994270486649713623755557 LowerField15_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
