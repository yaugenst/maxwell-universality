import Maxwell.Certificate.ProjectionWitness.LowerResult26
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField26Rows : Fin 20 → ℤ := ![6320487843260307061855755088353, 13505415621610356597655899000600, 13807469117936081790742247170586, 1411122440193766735923950047190, 357511322017886849673693372404, 147532727920049942453708378994, 55921177562149695242141849782, 25717018011212806934360828119, 5960245053747333748093865010, 6274928999362047404542585888, 6274928999362009828240322674, 5960245053747275017256459754, 25717018011212832865407202836, 55921177562149898658408795387, 147532727920050719854421280855, 357511322017884512444737609836, 1411122440193771585024108598031, 13807469117936090428614149782387, 13505415621610405920552128269246, 6320487843260272274450965173107]
theorem LowerField26X0 : highNormUpperX LowerResult26 0 = LowerField26Rows 0 := by decide +kernel
theorem LowerField26X1 : highNormUpperX LowerResult26 1 = LowerField26Rows 1 := by decide +kernel
theorem LowerField26X2 : highNormUpperX LowerResult26 2 = LowerField26Rows 2 := by decide +kernel
theorem LowerField26X3 : highNormUpperX LowerResult26 3 = LowerField26Rows 3 := by decide +kernel
theorem LowerField26X4 : highNormUpperX LowerResult26 4 = LowerField26Rows 4 := by decide +kernel
theorem LowerField26X5 : highNormUpperX LowerResult26 5 = LowerField26Rows 5 := by decide +kernel
theorem LowerField26X6 : highNormUpperX LowerResult26 6 = LowerField26Rows 6 := by decide +kernel
theorem LowerField26X7 : highNormUpperX LowerResult26 7 = LowerField26Rows 7 := by decide +kernel
theorem LowerField26X8 : highNormUpperX LowerResult26 8 = LowerField26Rows 8 := by decide +kernel
theorem LowerField26X9 : highNormUpperX LowerResult26 9 = LowerField26Rows 9 := by decide +kernel
theorem LowerField26X10 : highNormUpperX LowerResult26 10 = LowerField26Rows 10 := by decide +kernel
theorem LowerField26X11 : highNormUpperX LowerResult26 11 = LowerField26Rows 11 := by decide +kernel
theorem LowerField26X12 : highNormUpperX LowerResult26 12 = LowerField26Rows 12 := by decide +kernel
theorem LowerField26X13 : highNormUpperX LowerResult26 13 = LowerField26Rows 13 := by decide +kernel
theorem LowerField26X14 : highNormUpperX LowerResult26 14 = LowerField26Rows 14 := by decide +kernel
theorem LowerField26X15 : highNormUpperX LowerResult26 15 = LowerField26Rows 15 := by decide +kernel
theorem LowerField26X16 : highNormUpperX LowerResult26 16 = LowerField26Rows 16 := by decide +kernel
theorem LowerField26X17 : highNormUpperX LowerResult26 17 = LowerField26Rows 17 := by decide +kernel
theorem LowerField26X18 : highNormUpperX LowerResult26 18 = LowerField26Rows 18 := by decide +kernel
theorem LowerField26X19 : highNormUpperX LowerResult26 19 = LowerField26Rows 19 := by decide +kernel
theorem LowerField26_rows (x : Fin 20) : highNormUpperX LowerResult26 x = LowerField26Rows x := by
  fin_cases x
  · exact LowerField26X0
  · exact LowerField26X1
  · exact LowerField26X2
  · exact LowerField26X3
  · exact LowerField26X4
  · exact LowerField26X5
  · exact LowerField26X6
  · exact LowerField26X7
  · exact LowerField26X8
  · exact LowerField26X9
  · exact LowerField26X10
  · exact LowerField26X11
  · exact LowerField26X12
  · exact LowerField26X13
  · exact LowerField26X14
  · exact LowerField26X15
  · exact LowerField26X16
  · exact LowerField26X17
  · exact LowerField26X18
  · exact LowerField26X19
theorem LowerField26_bound : highNormUpper LowerResult26 ≤ 71286824885129868318944215681039 :=
  highNormUpper_le_of_rows LowerResult26 LowerField26Rows 71286824885129868318944215681039 LowerField26_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
