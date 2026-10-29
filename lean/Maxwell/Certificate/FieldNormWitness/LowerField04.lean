import Maxwell.Certificate.ProjectionWitness.LowerResult4
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField04Rows : Fin 20 → ℤ := ![25120046050712498936111335387104, 14194751552405919390276981688493, 19493206887824681806523442641882, 432537659151671753805771438575, 645512176199135940693376974214, 79188840765506590671789052135, 80411893361245903256852434521, 21601906516886379187777426366, 13538001301833308287415065459, 6027550499155182279923131562, 6027550499154447785061878048, 13538001301833729067887268103, 21601906516886903421855351875, 80411893361245919206298653639, 79188840765507658156573016762, 645512176199128972306335606442, 432537659151686726874520815632, 19493206887824740539109635526534, 14194751552405719818157183210958, 25120046050712359535333048760821]
theorem LowerField04X0 : highNormUpperX LowerResult4 0 = LowerField04Rows 0 := by decide +kernel
theorem LowerField04X1 : highNormUpperX LowerResult4 1 = LowerField04Rows 1 := by decide +kernel
theorem LowerField04X2 : highNormUpperX LowerResult4 2 = LowerField04Rows 2 := by decide +kernel
theorem LowerField04X3 : highNormUpperX LowerResult4 3 = LowerField04Rows 3 := by decide +kernel
theorem LowerField04X4 : highNormUpperX LowerResult4 4 = LowerField04Rows 4 := by decide +kernel
theorem LowerField04X5 : highNormUpperX LowerResult4 5 = LowerField04Rows 5 := by decide +kernel
theorem LowerField04X6 : highNormUpperX LowerResult4 6 = LowerField04Rows 6 := by decide +kernel
theorem LowerField04X7 : highNormUpperX LowerResult4 7 = LowerField04Rows 7 := by decide +kernel
theorem LowerField04X8 : highNormUpperX LowerResult4 8 = LowerField04Rows 8 := by decide +kernel
theorem LowerField04X9 : highNormUpperX LowerResult4 9 = LowerField04Rows 9 := by decide +kernel
theorem LowerField04X10 : highNormUpperX LowerResult4 10 = LowerField04Rows 10 := by decide +kernel
theorem LowerField04X11 : highNormUpperX LowerResult4 11 = LowerField04Rows 11 := by decide +kernel
theorem LowerField04X12 : highNormUpperX LowerResult4 12 = LowerField04Rows 12 := by decide +kernel
theorem LowerField04X13 : highNormUpperX LowerResult4 13 = LowerField04Rows 13 := by decide +kernel
theorem LowerField04X14 : highNormUpperX LowerResult4 14 = LowerField04Rows 14 := by decide +kernel
theorem LowerField04X15 : highNormUpperX LowerResult4 15 = LowerField04Rows 15 := by decide +kernel
theorem LowerField04X16 : highNormUpperX LowerResult4 16 = LowerField04Rows 16 := by decide +kernel
theorem LowerField04X17 : highNormUpperX LowerResult4 17 = LowerField04Rows 17 := by decide +kernel
theorem LowerField04X18 : highNormUpperX LowerResult4 18 = LowerField04Rows 18 := by decide +kernel
theorem LowerField04X19 : highNormUpperX LowerResult4 19 = LowerField04Rows 19 := by decide +kernel
theorem LowerField04_rows (x : Fin 20) : highNormUpperX LowerResult4 x = LowerField04Rows x := by
  fin_cases x
  · exact LowerField04X0
  · exact LowerField04X1
  · exact LowerField04X2
  · exact LowerField04X3
  · exact LowerField04X4
  · exact LowerField04X5
  · exact LowerField04X6
  · exact LowerField04X7
  · exact LowerField04X8
  · exact LowerField04X9
  · exact LowerField04X10
  · exact LowerField04X11
  · exact LowerField04X12
  · exact LowerField04X13
  · exact LowerField04X14
  · exact LowerField04X15
  · exact LowerField04X16
  · exact LowerField04X17
  · exact LowerField04X18
  · exact LowerField04X19
theorem LowerField04_bound : highNormUpper LowerResult4 ≤ 120173645037476799440513065329125 :=
  highNormUpper_le_of_rows LowerResult4 LowerField04Rows 120173645037476799440513065329125 LowerField04_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
