import Maxwell.Certificate.AppliedWitness.LowerApplied24
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied24Rows : Fin 20 → ℤ := ![40351421528759, 225535396857586, 256155315734611, 299855126439290, 354500948750426, 81356577843208, 428223016069237, 431300550304043, 425083782399738, 411300900703870, 85033662473426, 441804606741443, 435642473925989, 420797933151181, 398175775800891, 72419241774753, 304879948640087, 252825058977065, 215512751742469, 194563942646082]
theorem LowerApplied24X0 : highNormUpperX LowerApplied24 0 = LowerApplied24Rows 0 := by decide +kernel
theorem LowerApplied24X1 : highNormUpperX LowerApplied24 1 = LowerApplied24Rows 1 := by decide +kernel
theorem LowerApplied24X2 : highNormUpperX LowerApplied24 2 = LowerApplied24Rows 2 := by decide +kernel
theorem LowerApplied24X3 : highNormUpperX LowerApplied24 3 = LowerApplied24Rows 3 := by decide +kernel
theorem LowerApplied24X4 : highNormUpperX LowerApplied24 4 = LowerApplied24Rows 4 := by decide +kernel
theorem LowerApplied24X5 : highNormUpperX LowerApplied24 5 = LowerApplied24Rows 5 := by decide +kernel
theorem LowerApplied24X6 : highNormUpperX LowerApplied24 6 = LowerApplied24Rows 6 := by decide +kernel
theorem LowerApplied24X7 : highNormUpperX LowerApplied24 7 = LowerApplied24Rows 7 := by decide +kernel
theorem LowerApplied24X8 : highNormUpperX LowerApplied24 8 = LowerApplied24Rows 8 := by decide +kernel
theorem LowerApplied24X9 : highNormUpperX LowerApplied24 9 = LowerApplied24Rows 9 := by decide +kernel
theorem LowerApplied24X10 : highNormUpperX LowerApplied24 10 = LowerApplied24Rows 10 := by decide +kernel
theorem LowerApplied24X11 : highNormUpperX LowerApplied24 11 = LowerApplied24Rows 11 := by decide +kernel
theorem LowerApplied24X12 : highNormUpperX LowerApplied24 12 = LowerApplied24Rows 12 := by decide +kernel
theorem LowerApplied24X13 : highNormUpperX LowerApplied24 13 = LowerApplied24Rows 13 := by decide +kernel
theorem LowerApplied24X14 : highNormUpperX LowerApplied24 14 = LowerApplied24Rows 14 := by decide +kernel
theorem LowerApplied24X15 : highNormUpperX LowerApplied24 15 = LowerApplied24Rows 15 := by decide +kernel
theorem LowerApplied24X16 : highNormUpperX LowerApplied24 16 = LowerApplied24Rows 16 := by decide +kernel
theorem LowerApplied24X17 : highNormUpperX LowerApplied24 17 = LowerApplied24Rows 17 := by decide +kernel
theorem LowerApplied24X18 : highNormUpperX LowerApplied24 18 = LowerApplied24Rows 18 := by decide +kernel
theorem LowerApplied24X19 : highNormUpperX LowerApplied24 19 = LowerApplied24Rows 19 := by decide +kernel
theorem LowerApplied24_rows (x : Fin 20) : highNormUpperX LowerApplied24 x = LowerApplied24Rows x := by
  fin_cases x
  · exact LowerApplied24X0
  · exact LowerApplied24X1
  · exact LowerApplied24X2
  · exact LowerApplied24X3
  · exact LowerApplied24X4
  · exact LowerApplied24X5
  · exact LowerApplied24X6
  · exact LowerApplied24X7
  · exact LowerApplied24X8
  · exact LowerApplied24X9
  · exact LowerApplied24X10
  · exact LowerApplied24X11
  · exact LowerApplied24X12
  · exact LowerApplied24X13
  · exact LowerApplied24X14
  · exact LowerApplied24X15
  · exact LowerApplied24X16
  · exact LowerApplied24X17
  · exact LowerApplied24X18
  · exact LowerApplied24X19
theorem LowerApplied24_bound : highNormUpper LowerApplied24 ≤ 5775318432504154 :=
  highNormUpper_le_of_rows LowerApplied24 LowerApplied24Rows 5775318432504154 LowerApplied24_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
