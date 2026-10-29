import Maxwell.Certificate.ProjectionWitness.LowerResult0
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField00Rows : Fin 20 → ℤ := ![8955709632508592923669901979369, 13156454630505967791883095314674, 1201604257445822723221374809328, 571289794586958006960805501676, 79774688258284330676872752289, 75103735850582695360492861613, 15285667393086930256669799337, 22606806778486472692656324783, 6944825305165425254419132590, 4651911611418152737768167933, 4651911611418154536582045656, 6944825305165274198335316745, 22606806778485931679851956751, 15285667393086810642538060323, 75103735850581802157801202278, 79774688258284062979090561355, 571289794586941481506632103144, 1201604257445811519332832974026, 13156454630505706744482689609816, 8955709632508509430556084430357]
theorem LowerField00X0 : highNormUpperX LowerResult0 0 = LowerField00Rows 0 := by decide +kernel
theorem LowerField00X1 : highNormUpperX LowerResult0 1 = LowerField00Rows 1 := by decide +kernel
theorem LowerField00X2 : highNormUpperX LowerResult0 2 = LowerField00Rows 2 := by decide +kernel
theorem LowerField00X3 : highNormUpperX LowerResult0 3 = LowerField00Rows 3 := by decide +kernel
theorem LowerField00X4 : highNormUpperX LowerResult0 4 = LowerField00Rows 4 := by decide +kernel
theorem LowerField00X5 : highNormUpperX LowerResult0 5 = LowerField00Rows 5 := by decide +kernel
theorem LowerField00X6 : highNormUpperX LowerResult0 6 = LowerField00Rows 6 := by decide +kernel
theorem LowerField00X7 : highNormUpperX LowerResult0 7 = LowerField00Rows 7 := by decide +kernel
theorem LowerField00X8 : highNormUpperX LowerResult0 8 = LowerField00Rows 8 := by decide +kernel
theorem LowerField00X9 : highNormUpperX LowerResult0 9 = LowerField00Rows 9 := by decide +kernel
theorem LowerField00X10 : highNormUpperX LowerResult0 10 = LowerField00Rows 10 := by decide +kernel
theorem LowerField00X11 : highNormUpperX LowerResult0 11 = LowerField00Rows 11 := by decide +kernel
theorem LowerField00X12 : highNormUpperX LowerResult0 12 = LowerField00Rows 12 := by decide +kernel
theorem LowerField00X13 : highNormUpperX LowerResult0 13 = LowerField00Rows 13 := by decide +kernel
theorem LowerField00X14 : highNormUpperX LowerResult0 14 = LowerField00Rows 14 := by decide +kernel
theorem LowerField00X15 : highNormUpperX LowerResult0 15 = LowerField00Rows 15 := by decide +kernel
theorem LowerField00X16 : highNormUpperX LowerResult0 16 = LowerField00Rows 16 := by decide +kernel
theorem LowerField00X17 : highNormUpperX LowerResult0 17 = LowerField00Rows 17 := by decide +kernel
theorem LowerField00X18 : highNormUpperX LowerResult0 18 = LowerField00Rows 18 := by decide +kernel
theorem LowerField00X19 : highNormUpperX LowerResult0 19 = LowerField00Rows 19 := by decide +kernel
theorem LowerField00_rows (x : Fin 20) : highNormUpperX LowerResult0 x = LowerField00Rows x := by
  fin_cases x
  · exact LowerField00X0
  · exact LowerField00X1
  · exact LowerField00X2
  · exact LowerField00X3
  · exact LowerField00X4
  · exact LowerField00X5
  · exact LowerField00X6
  · exact LowerField00X7
  · exact LowerField00X8
  · exact LowerField00X9
  · exact LowerField00X10
  · exact LowerField00X11
  · exact LowerField00X12
  · exact LowerField00X13
  · exact LowerField00X14
  · exact LowerField00X15
  · exact LowerField00X16
  · exact LowerField00X17
  · exact LowerField00X18
  · exact LowerField00X19
theorem LowerField00_bound : highNormUpper LowerResult0 ≤ 48178851900488356664786494904043 :=
  highNormUpper_le_of_rows LowerResult0 LowerField00Rows 48178851900488356664786494904043 LowerField00_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
