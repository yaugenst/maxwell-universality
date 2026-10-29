import Maxwell.Certificate.ProjectionWitness.LowerResult22
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField22Rows : Fin 20 → ℤ := ![27597438698183591937177384762616, 12512701126515761910552857970570, 14677397816344437061714680447804, 964054797684164984171997496712, 220104588782125429818498041618, 122155589276166963839292803700, 31680727893403349995865191430, 30424203135257273042280161865, 9613578536072942240107074413, 12156033482494917778499398458, 12156033482494874567398566677, 9613578536072988925904422982, 30424203135257354902735063840, 31680727893404005471022298421, 122155589276168885287020093967, 220104588782128812955223714683, 964054797684180307125872506781, 14677397816344545112640148387362, 12512701126515752443239158131832, 27597438698183551708987032617843]
theorem LowerField22X0 : highNormUpperX LowerResult22 0 = LowerField22Rows 0 := by decide +kernel
theorem LowerField22X1 : highNormUpperX LowerResult22 1 = LowerField22Rows 1 := by decide +kernel
theorem LowerField22X2 : highNormUpperX LowerResult22 2 = LowerField22Rows 2 := by decide +kernel
theorem LowerField22X3 : highNormUpperX LowerResult22 3 = LowerField22Rows 3 := by decide +kernel
theorem LowerField22X4 : highNormUpperX LowerResult22 4 = LowerField22Rows 4 := by decide +kernel
theorem LowerField22X5 : highNormUpperX LowerResult22 5 = LowerField22Rows 5 := by decide +kernel
theorem LowerField22X6 : highNormUpperX LowerResult22 6 = LowerField22Rows 6 := by decide +kernel
theorem LowerField22X7 : highNormUpperX LowerResult22 7 = LowerField22Rows 7 := by decide +kernel
theorem LowerField22X8 : highNormUpperX LowerResult22 8 = LowerField22Rows 8 := by decide +kernel
theorem LowerField22X9 : highNormUpperX LowerResult22 9 = LowerField22Rows 9 := by decide +kernel
theorem LowerField22X10 : highNormUpperX LowerResult22 10 = LowerField22Rows 10 := by decide +kernel
theorem LowerField22X11 : highNormUpperX LowerResult22 11 = LowerField22Rows 11 := by decide +kernel
theorem LowerField22X12 : highNormUpperX LowerResult22 12 = LowerField22Rows 12 := by decide +kernel
theorem LowerField22X13 : highNormUpperX LowerResult22 13 = LowerField22Rows 13 := by decide +kernel
theorem LowerField22X14 : highNormUpperX LowerResult22 14 = LowerField22Rows 14 := by decide +kernel
theorem LowerField22X15 : highNormUpperX LowerResult22 15 = LowerField22Rows 15 := by decide +kernel
theorem LowerField22X16 : highNormUpperX LowerResult22 16 = LowerField22Rows 16 := by decide +kernel
theorem LowerField22X17 : highNormUpperX LowerResult22 17 = LowerField22Rows 17 := by decide +kernel
theorem LowerField22X18 : highNormUpperX LowerResult22 18 = LowerField22Rows 18 := by decide +kernel
theorem LowerField22X19 : highNormUpperX LowerResult22 19 = LowerField22Rows 19 := by decide +kernel
theorem LowerField22_rows (x : Fin 20) : highNormUpperX LowerResult22 x = LowerField22Rows x := by
  fin_cases x
  · exact LowerField22X0
  · exact LowerField22X1
  · exact LowerField22X2
  · exact LowerField22X3
  · exact LowerField22X4
  · exact LowerField22X5
  · exact LowerField22X6
  · exact LowerField22X7
  · exact LowerField22X8
  · exact LowerField22X9
  · exact LowerField22X10
  · exact LowerField22X11
  · exact LowerField22X12
  · exact LowerField22X13
  · exact LowerField22X14
  · exact LowerField22X15
  · exact LowerField22X16
  · exact LowerField22X17
  · exact LowerField22X18
  · exact LowerField22X19
theorem LowerField22_bound : highNormUpper LowerResult22 ≤ 112355454319667033264432979153574 :=
  highNormUpper_le_of_rows LowerResult22 LowerField22Rows 112355454319667033264432979153574 LowerField22_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
