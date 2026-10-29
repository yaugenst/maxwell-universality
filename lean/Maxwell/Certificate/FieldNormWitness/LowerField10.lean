import Maxwell.Certificate.ProjectionWitness.LowerResult10
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField10Rows : Fin 20 → ℤ := ![14066343586576741018943018214331, 16309569006222200061214898539581, 17242075791866743839157127161308, 560700781360059882799228011407, 603550609791377336061670121442, 76675518891074760215936306969, 78743270647629080478874302976, 17755970569671508151674039030, 12930599324296518817381595438, 4434798114445901291370190518, 4434798114446013481835162168, 12930599324296322533745419025, 17755970569671357771752100565, 78743270647628816268537639424, 76675518891075789392407466800, 603550609791372004604877432201, 560700781360059782724421723999, 17242075791866651845448392257394, 16309569006222092913340356456100, 14066343586576622043730000126215]
theorem LowerField10X0 : highNormUpperX LowerResult10 0 = LowerField10Rows 0 := by decide +kernel
theorem LowerField10X1 : highNormUpperX LowerResult10 1 = LowerField10Rows 1 := by decide +kernel
theorem LowerField10X2 : highNormUpperX LowerResult10 2 = LowerField10Rows 2 := by decide +kernel
theorem LowerField10X3 : highNormUpperX LowerResult10 3 = LowerField10Rows 3 := by decide +kernel
theorem LowerField10X4 : highNormUpperX LowerResult10 4 = LowerField10Rows 4 := by decide +kernel
theorem LowerField10X5 : highNormUpperX LowerResult10 5 = LowerField10Rows 5 := by decide +kernel
theorem LowerField10X6 : highNormUpperX LowerResult10 6 = LowerField10Rows 6 := by decide +kernel
theorem LowerField10X7 : highNormUpperX LowerResult10 7 = LowerField10Rows 7 := by decide +kernel
theorem LowerField10X8 : highNormUpperX LowerResult10 8 = LowerField10Rows 8 := by decide +kernel
theorem LowerField10X9 : highNormUpperX LowerResult10 9 = LowerField10Rows 9 := by decide +kernel
theorem LowerField10X10 : highNormUpperX LowerResult10 10 = LowerField10Rows 10 := by decide +kernel
theorem LowerField10X11 : highNormUpperX LowerResult10 11 = LowerField10Rows 11 := by decide +kernel
theorem LowerField10X12 : highNormUpperX LowerResult10 12 = LowerField10Rows 12 := by decide +kernel
theorem LowerField10X13 : highNormUpperX LowerResult10 13 = LowerField10Rows 13 := by decide +kernel
theorem LowerField10X14 : highNormUpperX LowerResult10 14 = LowerField10Rows 14 := by decide +kernel
theorem LowerField10X15 : highNormUpperX LowerResult10 15 = LowerField10Rows 15 := by decide +kernel
theorem LowerField10X16 : highNormUpperX LowerResult10 16 = LowerField10Rows 16 := by decide +kernel
theorem LowerField10X17 : highNormUpperX LowerResult10 17 = LowerField10Rows 17 := by decide +kernel
theorem LowerField10X18 : highNormUpperX LowerResult10 18 = LowerField10Rows 18 := by decide +kernel
theorem LowerField10X19 : highNormUpperX LowerResult10 19 = LowerField10Rows 19 := by decide +kernel
theorem LowerField10_rows (x : Fin 20) : highNormUpperX LowerResult10 x = LowerField10Rows x := by
  fin_cases x
  · exact LowerField10X0
  · exact LowerField10X1
  · exact LowerField10X2
  · exact LowerField10X3
  · exact LowerField10X4
  · exact LowerField10X5
  · exact LowerField10X6
  · exact LowerField10X7
  · exact LowerField10X8
  · exact LowerField10X9
  · exact LowerField10X10
  · exact LowerField10X11
  · exact LowerField10X12
  · exact LowerField10X13
  · exact LowerField10X14
  · exact LowerField10X15
  · exact LowerField10X16
  · exact LowerField10X17
  · exact LowerField10X18
  · exact LowerField10X19
theorem LowerField10_bound : highNormUpper LowerResult10 ≤ 97945559866728156796427504266891 :=
  highNormUpper_le_of_rows LowerResult10 LowerField10Rows 97945559866728156796427504266891 LowerField10_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
