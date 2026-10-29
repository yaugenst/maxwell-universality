import Maxwell.Certificate.ProjectionWitness.UpperResult26
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField26Rows : Fin 20 → ℤ := ![12482613905570132628503756114697, 4321993858200914438449031750392, 11831611909645974747038096357989, 883482341087513216394503929128, 200845293304626687409094843996, 100128722954162605788719283990, 37687923624046481965747643161, 23044882560476739255223742508, 12610812080850062688170179048, 11021888580117814728955169055, 11021888580117622558015733134, 12610812080850821828014704900, 23044882560476704024069547081, 37687923624048299804330910383, 100128722954164357231954453321, 200845293304639931058517064589, 883482341087546704793036608112, 11831611909646520266370880065653, 4321993858201064525090783474053, 12482613905570138947122651437254]
theorem UpperField26X0 : highNormUpperX UpperResult26 0 = UpperField26Rows 0 := by decide +kernel
theorem UpperField26X1 : highNormUpperX UpperResult26 1 = UpperField26Rows 1 := by decide +kernel
theorem UpperField26X2 : highNormUpperX UpperResult26 2 = UpperField26Rows 2 := by decide +kernel
theorem UpperField26X3 : highNormUpperX UpperResult26 3 = UpperField26Rows 3 := by decide +kernel
theorem UpperField26X4 : highNormUpperX UpperResult26 4 = UpperField26Rows 4 := by decide +kernel
theorem UpperField26X5 : highNormUpperX UpperResult26 5 = UpperField26Rows 5 := by decide +kernel
theorem UpperField26X6 : highNormUpperX UpperResult26 6 = UpperField26Rows 6 := by decide +kernel
theorem UpperField26X7 : highNormUpperX UpperResult26 7 = UpperField26Rows 7 := by decide +kernel
theorem UpperField26X8 : highNormUpperX UpperResult26 8 = UpperField26Rows 8 := by decide +kernel
theorem UpperField26X9 : highNormUpperX UpperResult26 9 = UpperField26Rows 9 := by decide +kernel
theorem UpperField26X10 : highNormUpperX UpperResult26 10 = UpperField26Rows 10 := by decide +kernel
theorem UpperField26X11 : highNormUpperX UpperResult26 11 = UpperField26Rows 11 := by decide +kernel
theorem UpperField26X12 : highNormUpperX UpperResult26 12 = UpperField26Rows 12 := by decide +kernel
theorem UpperField26X13 : highNormUpperX UpperResult26 13 = UpperField26Rows 13 := by decide +kernel
theorem UpperField26X14 : highNormUpperX UpperResult26 14 = UpperField26Rows 14 := by decide +kernel
theorem UpperField26X15 : highNormUpperX UpperResult26 15 = UpperField26Rows 15 := by decide +kernel
theorem UpperField26X16 : highNormUpperX UpperResult26 16 = UpperField26Rows 16 := by decide +kernel
theorem UpperField26X17 : highNormUpperX UpperResult26 17 = UpperField26Rows 17 := by decide +kernel
theorem UpperField26X18 : highNormUpperX UpperResult26 18 = UpperField26Rows 18 := by decide +kernel
theorem UpperField26X19 : highNormUpperX UpperResult26 19 = UpperField26Rows 19 := by decide +kernel
theorem UpperField26_rows (x : Fin 20) : highNormUpperX UpperResult26 x = UpperField26Rows x := by
  fin_cases x
  · exact UpperField26X0
  · exact UpperField26X1
  · exact UpperField26X2
  · exact UpperField26X3
  · exact UpperField26X4
  · exact UpperField26X5
  · exact UpperField26X6
  · exact UpperField26X7
  · exact UpperField26X8
  · exact UpperField26X9
  · exact UpperField26X10
  · exact UpperField26X11
  · exact UpperField26X12
  · exact UpperField26X13
  · exact UpperField26X14
  · exact UpperField26X15
  · exact UpperField26X16
  · exact UpperField26X17
  · exact UpperField26X18
  · exact UpperField26X19
theorem UpperField26_bound : highNormUpper UpperResult26 ≤ 59810083075218383602103553012444 :=
  highNormUpper_le_of_rows UpperResult26 UpperField26Rows 59810083075218383602103553012444 UpperField26_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
