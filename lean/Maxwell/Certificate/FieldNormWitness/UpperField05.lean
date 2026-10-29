import Maxwell.Certificate.ProjectionWitness.UpperResult5
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField05Rows : Fin 20 → ℤ := ![11251035751632977707264240404483, 12306444455617546613710250029991, 36445986123987032987170070920928, 791151507564904257591195360838, 956251478625866189026264742095, 123882358018429241062172615130, 113857135362232340807790263749, 28063941572802862246179428689, 14450439377370378475009622045, 9337871901347379795615975177, 9337871901346749363491559503, 14450439377369591621276931746, 28063941572801986678985789443, 113857135362229248129416613611, 123882358018425129106830619363, 956251478625836923039304121895, 791151507564854103311548112474, 36445986123985196817653333356887, 12306444455616876719111105000178, 11251035751633918700825384645177]
theorem UpperField05X0 : highNormUpperX UpperResult5 0 = UpperField05Rows 0 := by decide +kernel
theorem UpperField05X1 : highNormUpperX UpperResult5 1 = UpperField05Rows 1 := by decide +kernel
theorem UpperField05X2 : highNormUpperX UpperResult5 2 = UpperField05Rows 2 := by decide +kernel
theorem UpperField05X3 : highNormUpperX UpperResult5 3 = UpperField05Rows 3 := by decide +kernel
theorem UpperField05X4 : highNormUpperX UpperResult5 4 = UpperField05Rows 4 := by decide +kernel
theorem UpperField05X5 : highNormUpperX UpperResult5 5 = UpperField05Rows 5 := by decide +kernel
theorem UpperField05X6 : highNormUpperX UpperResult5 6 = UpperField05Rows 6 := by decide +kernel
theorem UpperField05X7 : highNormUpperX UpperResult5 7 = UpperField05Rows 7 := by decide +kernel
theorem UpperField05X8 : highNormUpperX UpperResult5 8 = UpperField05Rows 8 := by decide +kernel
theorem UpperField05X9 : highNormUpperX UpperResult5 9 = UpperField05Rows 9 := by decide +kernel
theorem UpperField05X10 : highNormUpperX UpperResult5 10 = UpperField05Rows 10 := by decide +kernel
theorem UpperField05X11 : highNormUpperX UpperResult5 11 = UpperField05Rows 11 := by decide +kernel
theorem UpperField05X12 : highNormUpperX UpperResult5 12 = UpperField05Rows 12 := by decide +kernel
theorem UpperField05X13 : highNormUpperX UpperResult5 13 = UpperField05Rows 13 := by decide +kernel
theorem UpperField05X14 : highNormUpperX UpperResult5 14 = UpperField05Rows 14 := by decide +kernel
theorem UpperField05X15 : highNormUpperX UpperResult5 15 = UpperField05Rows 15 := by decide +kernel
theorem UpperField05X16 : highNormUpperX UpperResult5 16 = UpperField05Rows 16 := by decide +kernel
theorem UpperField05X17 : highNormUpperX UpperResult5 17 = UpperField05Rows 17 := by decide +kernel
theorem UpperField05X18 : highNormUpperX UpperResult5 18 = UpperField05Rows 18 := by decide +kernel
theorem UpperField05X19 : highNormUpperX UpperResult5 19 = UpperField05Rows 19 := by decide +kernel
theorem UpperField05_rows (x : Fin 20) : highNormUpperX UpperResult5 x = UpperField05Rows x := by
  fin_cases x
  · exact UpperField05X0
  · exact UpperField05X1
  · exact UpperField05X2
  · exact UpperField05X3
  · exact UpperField05X4
  · exact UpperField05X5
  · exact UpperField05X6
  · exact UpperField05X7
  · exact UpperField05X8
  · exact UpperField05X9
  · exact UpperField05X10
  · exact UpperField05X11
  · exact UpperField05X12
  · exact UpperField05X13
  · exact UpperField05X14
  · exact UpperField05X15
  · exact UpperField05X16
  · exact UpperField05X17
  · exact UpperField05X18
  · exact UpperField05X19
theorem UpperField05_bound : highNormUpper UpperResult5 ≤ 124080922127319365925989466113402 :=
  highNormUpper_le_of_rows UpperResult5 UpperField05Rows 124080922127319365925989466113402 UpperField05_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
