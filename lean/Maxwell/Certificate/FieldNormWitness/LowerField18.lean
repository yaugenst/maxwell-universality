import Maxwell.Certificate.ProjectionWitness.LowerResult18
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField18Rows : Fin 20 → ℤ := ![17236838209037316171371986330332, 6716808102739873690189817153328, 24838390510043100381785459050308, 1433136722514832558275852552211, 487487418870062636740349791004, 213297094311500988344762703712, 55474602329920382609273640191, 39780991626320570421799161317, 8477031532789200995121504108, 8652875574524854820741252349, 8652875574524871711549704808, 8477031532789432185135761741, 39780991626320125849262932550, 55474602329920835026190647023, 213297094311500876797614251113, 487487418870063669804905929596, 1433136722514832150812251746001, 24838390510043116475335970190062, 6716808102739851220349189665823, 17236838209037220816650759087430]
theorem LowerField18X0 : highNormUpperX LowerResult18 0 = LowerField18Rows 0 := by decide +kernel
theorem LowerField18X1 : highNormUpperX LowerResult18 1 = LowerField18Rows 1 := by decide +kernel
theorem LowerField18X2 : highNormUpperX LowerResult18 2 = LowerField18Rows 2 := by decide +kernel
theorem LowerField18X3 : highNormUpperX LowerResult18 3 = LowerField18Rows 3 := by decide +kernel
theorem LowerField18X4 : highNormUpperX LowerResult18 4 = LowerField18Rows 4 := by decide +kernel
theorem LowerField18X5 : highNormUpperX LowerResult18 5 = LowerField18Rows 5 := by decide +kernel
theorem LowerField18X6 : highNormUpperX LowerResult18 6 = LowerField18Rows 6 := by decide +kernel
theorem LowerField18X7 : highNormUpperX LowerResult18 7 = LowerField18Rows 7 := by decide +kernel
theorem LowerField18X8 : highNormUpperX LowerResult18 8 = LowerField18Rows 8 := by decide +kernel
theorem LowerField18X9 : highNormUpperX LowerResult18 9 = LowerField18Rows 9 := by decide +kernel
theorem LowerField18X10 : highNormUpperX LowerResult18 10 = LowerField18Rows 10 := by decide +kernel
theorem LowerField18X11 : highNormUpperX LowerResult18 11 = LowerField18Rows 11 := by decide +kernel
theorem LowerField18X12 : highNormUpperX LowerResult18 12 = LowerField18Rows 12 := by decide +kernel
theorem LowerField18X13 : highNormUpperX LowerResult18 13 = LowerField18Rows 13 := by decide +kernel
theorem LowerField18X14 : highNormUpperX LowerResult18 14 = LowerField18Rows 14 := by decide +kernel
theorem LowerField18X15 : highNormUpperX LowerResult18 15 = LowerField18Rows 15 := by decide +kernel
theorem LowerField18X16 : highNormUpperX LowerResult18 16 = LowerField18Rows 16 := by decide +kernel
theorem LowerField18X17 : highNormUpperX LowerResult18 17 = LowerField18Rows 17 := by decide +kernel
theorem LowerField18X18 : highNormUpperX LowerResult18 18 = LowerField18Rows 18 := by decide +kernel
theorem LowerField18X19 : highNormUpperX LowerResult18 19 = LowerField18Rows 19 := by decide +kernel
theorem LowerField18_rows (x : Fin 20) : highNormUpperX LowerResult18 x = LowerField18Rows x := by
  fin_cases x
  · exact LowerField18X0
  · exact LowerField18X1
  · exact LowerField18X2
  · exact LowerField18X3
  · exact LowerField18X4
  · exact LowerField18X5
  · exact LowerField18X6
  · exact LowerField18X7
  · exact LowerField18X8
  · exact LowerField18X9
  · exact LowerField18X10
  · exact LowerField18X11
  · exact LowerField18X12
  · exact LowerField18X13
  · exact LowerField18X14
  · exact LowerField18X15
  · exact LowerField18X16
  · exact LowerField18X17
  · exact LowerField18X18
  · exact LowerField18X19
theorem LowerField18_bound : highNormUpper LowerResult18 ≤ 102076687117160381910077993055007 :=
  highNormUpper_le_of_rows LowerResult18 LowerField18Rows 102076687117160381910077993055007 LowerField18_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
