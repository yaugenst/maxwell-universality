import Maxwell.Certificate.AppliedWitness.LowerApplied14
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied14Rows : Fin 20 → ℤ := ![40205686572114, 224723144322900, 255220143375868, 298760809544917, 353219529321211, 81059567323110, 426671580734169, 429718398448295, 423526803541948, 409811370260640, 84723196883698, 440205940043639, 434043856526905, 419255885108738, 396735149443925, 72154590801781, 303780445246923, 251902384137957, 214727162652665, 193865042534199]
theorem LowerApplied14X0 : highNormUpperX LowerApplied14 0 = LowerApplied14Rows 0 := by decide +kernel
theorem LowerApplied14X1 : highNormUpperX LowerApplied14 1 = LowerApplied14Rows 1 := by decide +kernel
theorem LowerApplied14X2 : highNormUpperX LowerApplied14 2 = LowerApplied14Rows 2 := by decide +kernel
theorem LowerApplied14X3 : highNormUpperX LowerApplied14 3 = LowerApplied14Rows 3 := by decide +kernel
theorem LowerApplied14X4 : highNormUpperX LowerApplied14 4 = LowerApplied14Rows 4 := by decide +kernel
theorem LowerApplied14X5 : highNormUpperX LowerApplied14 5 = LowerApplied14Rows 5 := by decide +kernel
theorem LowerApplied14X6 : highNormUpperX LowerApplied14 6 = LowerApplied14Rows 6 := by decide +kernel
theorem LowerApplied14X7 : highNormUpperX LowerApplied14 7 = LowerApplied14Rows 7 := by decide +kernel
theorem LowerApplied14X8 : highNormUpperX LowerApplied14 8 = LowerApplied14Rows 8 := by decide +kernel
theorem LowerApplied14X9 : highNormUpperX LowerApplied14 9 = LowerApplied14Rows 9 := by decide +kernel
theorem LowerApplied14X10 : highNormUpperX LowerApplied14 10 = LowerApplied14Rows 10 := by decide +kernel
theorem LowerApplied14X11 : highNormUpperX LowerApplied14 11 = LowerApplied14Rows 11 := by decide +kernel
theorem LowerApplied14X12 : highNormUpperX LowerApplied14 12 = LowerApplied14Rows 12 := by decide +kernel
theorem LowerApplied14X13 : highNormUpperX LowerApplied14 13 = LowerApplied14Rows 13 := by decide +kernel
theorem LowerApplied14X14 : highNormUpperX LowerApplied14 14 = LowerApplied14Rows 14 := by decide +kernel
theorem LowerApplied14X15 : highNormUpperX LowerApplied14 15 = LowerApplied14Rows 15 := by decide +kernel
theorem LowerApplied14X16 : highNormUpperX LowerApplied14 16 = LowerApplied14Rows 16 := by decide +kernel
theorem LowerApplied14X17 : highNormUpperX LowerApplied14 17 = LowerApplied14Rows 17 := by decide +kernel
theorem LowerApplied14X18 : highNormUpperX LowerApplied14 18 = LowerApplied14Rows 18 := by decide +kernel
theorem LowerApplied14X19 : highNormUpperX LowerApplied14 19 = LowerApplied14Rows 19 := by decide +kernel
theorem LowerApplied14_rows (x : Fin 20) : highNormUpperX LowerApplied14 x = LowerApplied14Rows x := by
  fin_cases x
  · exact LowerApplied14X0
  · exact LowerApplied14X1
  · exact LowerApplied14X2
  · exact LowerApplied14X3
  · exact LowerApplied14X4
  · exact LowerApplied14X5
  · exact LowerApplied14X6
  · exact LowerApplied14X7
  · exact LowerApplied14X8
  · exact LowerApplied14X9
  · exact LowerApplied14X10
  · exact LowerApplied14X11
  · exact LowerApplied14X12
  · exact LowerApplied14X13
  · exact LowerApplied14X14
  · exact LowerApplied14X15
  · exact LowerApplied14X16
  · exact LowerApplied14X17
  · exact LowerApplied14X18
  · exact LowerApplied14X19
theorem LowerApplied14_bound : highNormUpper LowerApplied14 ≤ 5754310686825602 :=
  highNormUpper_le_of_rows LowerApplied14 LowerApplied14Rows 5754310686825602 LowerApplied14_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
