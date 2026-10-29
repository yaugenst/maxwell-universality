import Maxwell.Certificate.AppliedWitness.LowerApplied3
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied03Rows : Fin 20 → ℤ := ![43287434276292, 241889571433338, 274727701682771, 321655084911701, 380357186802921, 87299925667309, 459564133395256, 462859018208015, 456173679106467, 441354770070165, 91242178901780, 474137031571731, 467516169446690, 451573716771845, 427278396675138, 77699560917532, 327058304009731, 271154830371152, 231127810659663, 208714525541058]
theorem LowerApplied03X0 : highNormUpperX LowerApplied3 0 = LowerApplied03Rows 0 := by decide +kernel
theorem LowerApplied03X1 : highNormUpperX LowerApplied3 1 = LowerApplied03Rows 1 := by decide +kernel
theorem LowerApplied03X2 : highNormUpperX LowerApplied3 2 = LowerApplied03Rows 2 := by decide +kernel
theorem LowerApplied03X3 : highNormUpperX LowerApplied3 3 = LowerApplied03Rows 3 := by decide +kernel
theorem LowerApplied03X4 : highNormUpperX LowerApplied3 4 = LowerApplied03Rows 4 := by decide +kernel
theorem LowerApplied03X5 : highNormUpperX LowerApplied3 5 = LowerApplied03Rows 5 := by decide +kernel
theorem LowerApplied03X6 : highNormUpperX LowerApplied3 6 = LowerApplied03Rows 6 := by decide +kernel
theorem LowerApplied03X7 : highNormUpperX LowerApplied3 7 = LowerApplied03Rows 7 := by decide +kernel
theorem LowerApplied03X8 : highNormUpperX LowerApplied3 8 = LowerApplied03Rows 8 := by decide +kernel
theorem LowerApplied03X9 : highNormUpperX LowerApplied3 9 = LowerApplied03Rows 9 := by decide +kernel
theorem LowerApplied03X10 : highNormUpperX LowerApplied3 10 = LowerApplied03Rows 10 := by decide +kernel
theorem LowerApplied03X11 : highNormUpperX LowerApplied3 11 = LowerApplied03Rows 11 := by decide +kernel
theorem LowerApplied03X12 : highNormUpperX LowerApplied3 12 = LowerApplied03Rows 12 := by decide +kernel
theorem LowerApplied03X13 : highNormUpperX LowerApplied3 13 = LowerApplied03Rows 13 := by decide +kernel
theorem LowerApplied03X14 : highNormUpperX LowerApplied3 14 = LowerApplied03Rows 14 := by decide +kernel
theorem LowerApplied03X15 : highNormUpperX LowerApplied3 15 = LowerApplied03Rows 15 := by decide +kernel
theorem LowerApplied03X16 : highNormUpperX LowerApplied3 16 = LowerApplied03Rows 16 := by decide +kernel
theorem LowerApplied03X17 : highNormUpperX LowerApplied3 17 = LowerApplied03Rows 17 := by decide +kernel
theorem LowerApplied03X18 : highNormUpperX LowerApplied3 18 = LowerApplied03Rows 18 := by decide +kernel
theorem LowerApplied03X19 : highNormUpperX LowerApplied3 19 = LowerApplied03Rows 19 := by decide +kernel
theorem LowerApplied03_rows (x : Fin 20) : highNormUpperX LowerApplied3 x = LowerApplied03Rows x := by
  fin_cases x
  · exact LowerApplied03X0
  · exact LowerApplied03X1
  · exact LowerApplied03X2
  · exact LowerApplied03X3
  · exact LowerApplied03X4
  · exact LowerApplied03X5
  · exact LowerApplied03X6
  · exact LowerApplied03X7
  · exact LowerApplied03X8
  · exact LowerApplied03X9
  · exact LowerApplied03X10
  · exact LowerApplied03X11
  · exact LowerApplied03X12
  · exact LowerApplied03X13
  · exact LowerApplied03X14
  · exact LowerApplied03X15
  · exact LowerApplied03X16
  · exact LowerApplied03X17
  · exact LowerApplied03X18
  · exact LowerApplied03X19
theorem LowerApplied03_bound : highNormUpper LowerApplied3 ≤ 6196671030420555 :=
  highNormUpper_le_of_rows LowerApplied3 LowerApplied03Rows 6196671030420555 LowerApplied03_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
