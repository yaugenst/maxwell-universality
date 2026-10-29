import Maxwell.Certificate.AppliedWitness.LowerApplied6
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied06Rows : Fin 20 → ℤ := ![40393708259314, 225775406346693, 256413761356220, 300141923718235, 354827449059320, 81428123648215, 428569690322677, 431627134287765, 425415685735641, 411654461216631, 85109042021253, 442166611958782, 435974033703958, 421123399060154, 398516809182028, 72487317012251, 305183023910615, 253081625400402, 215735985700506, 194767983536426]
theorem LowerApplied06X0 : highNormUpperX LowerApplied6 0 = LowerApplied06Rows 0 := by decide +kernel
theorem LowerApplied06X1 : highNormUpperX LowerApplied6 1 = LowerApplied06Rows 1 := by decide +kernel
theorem LowerApplied06X2 : highNormUpperX LowerApplied6 2 = LowerApplied06Rows 2 := by decide +kernel
theorem LowerApplied06X3 : highNormUpperX LowerApplied6 3 = LowerApplied06Rows 3 := by decide +kernel
theorem LowerApplied06X4 : highNormUpperX LowerApplied6 4 = LowerApplied06Rows 4 := by decide +kernel
theorem LowerApplied06X5 : highNormUpperX LowerApplied6 5 = LowerApplied06Rows 5 := by decide +kernel
theorem LowerApplied06X6 : highNormUpperX LowerApplied6 6 = LowerApplied06Rows 6 := by decide +kernel
theorem LowerApplied06X7 : highNormUpperX LowerApplied6 7 = LowerApplied06Rows 7 := by decide +kernel
theorem LowerApplied06X8 : highNormUpperX LowerApplied6 8 = LowerApplied06Rows 8 := by decide +kernel
theorem LowerApplied06X9 : highNormUpperX LowerApplied6 9 = LowerApplied06Rows 9 := by decide +kernel
theorem LowerApplied06X10 : highNormUpperX LowerApplied6 10 = LowerApplied06Rows 10 := by decide +kernel
theorem LowerApplied06X11 : highNormUpperX LowerApplied6 11 = LowerApplied06Rows 11 := by decide +kernel
theorem LowerApplied06X12 : highNormUpperX LowerApplied6 12 = LowerApplied06Rows 12 := by decide +kernel
theorem LowerApplied06X13 : highNormUpperX LowerApplied6 13 = LowerApplied06Rows 13 := by decide +kernel
theorem LowerApplied06X14 : highNormUpperX LowerApplied6 14 = LowerApplied06Rows 14 := by decide +kernel
theorem LowerApplied06X15 : highNormUpperX LowerApplied6 15 = LowerApplied06Rows 15 := by decide +kernel
theorem LowerApplied06X16 : highNormUpperX LowerApplied6 16 = LowerApplied06Rows 16 := by decide +kernel
theorem LowerApplied06X17 : highNormUpperX LowerApplied6 17 = LowerApplied06Rows 17 := by decide +kernel
theorem LowerApplied06X18 : highNormUpperX LowerApplied6 18 = LowerApplied06Rows 18 := by decide +kernel
theorem LowerApplied06X19 : highNormUpperX LowerApplied6 19 = LowerApplied06Rows 19 := by decide +kernel
theorem LowerApplied06_rows (x : Fin 20) : highNormUpperX LowerApplied6 x = LowerApplied06Rows x := by
  fin_cases x
  · exact LowerApplied06X0
  · exact LowerApplied06X1
  · exact LowerApplied06X2
  · exact LowerApplied06X3
  · exact LowerApplied06X4
  · exact LowerApplied06X5
  · exact LowerApplied06X6
  · exact LowerApplied06X7
  · exact LowerApplied06X8
  · exact LowerApplied06X9
  · exact LowerApplied06X10
  · exact LowerApplied06X11
  · exact LowerApplied06X12
  · exact LowerApplied06X13
  · exact LowerApplied06X14
  · exact LowerApplied06X15
  · exact LowerApplied06X16
  · exact LowerApplied06X17
  · exact LowerApplied06X18
  · exact LowerApplied06X19
theorem LowerApplied06_bound : highNormUpper LowerApplied6 ≤ 5780393175437086 :=
  highNormUpper_le_of_rows LowerApplied6 LowerApplied06Rows 5780393175437086 LowerApplied06_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
