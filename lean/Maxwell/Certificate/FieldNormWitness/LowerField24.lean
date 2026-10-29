import Maxwell.Certificate.ProjectionWitness.LowerResult24
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField24Rows : Fin 20 → ℤ := ![34268312487313949564988911680026, 4948845784126040359709794041011, 20964649453418858851584547255670, 2053164278487901841918829282432, 297534713474412601200451252105, 231338867568879412486202626545, 42258165787563640145718165744, 41952388072237764171169112932, 9335911482128939782143508373, 6924347101450921750128041998, 6924347101451141107720018781, 9335911482129018122099621051, 41952388072238069364025044578, 42258165787563504874881868590, 231338867568880812650923791627, 297534713474414499604060322060, 2053164278487907292244546752124, 20964649453419028621288141350588, 4948845784126083459889859370260, 34268312487313732860239237508448]
theorem LowerField24X0 : highNormUpperX LowerResult24 0 = LowerField24Rows 0 := by decide +kernel
theorem LowerField24X1 : highNormUpperX LowerResult24 1 = LowerField24Rows 1 := by decide +kernel
theorem LowerField24X2 : highNormUpperX LowerResult24 2 = LowerField24Rows 2 := by decide +kernel
theorem LowerField24X3 : highNormUpperX LowerResult24 3 = LowerField24Rows 3 := by decide +kernel
theorem LowerField24X4 : highNormUpperX LowerResult24 4 = LowerField24Rows 4 := by decide +kernel
theorem LowerField24X5 : highNormUpperX LowerResult24 5 = LowerField24Rows 5 := by decide +kernel
theorem LowerField24X6 : highNormUpperX LowerResult24 6 = LowerField24Rows 6 := by decide +kernel
theorem LowerField24X7 : highNormUpperX LowerResult24 7 = LowerField24Rows 7 := by decide +kernel
theorem LowerField24X8 : highNormUpperX LowerResult24 8 = LowerField24Rows 8 := by decide +kernel
theorem LowerField24X9 : highNormUpperX LowerResult24 9 = LowerField24Rows 9 := by decide +kernel
theorem LowerField24X10 : highNormUpperX LowerResult24 10 = LowerField24Rows 10 := by decide +kernel
theorem LowerField24X11 : highNormUpperX LowerResult24 11 = LowerField24Rows 11 := by decide +kernel
theorem LowerField24X12 : highNormUpperX LowerResult24 12 = LowerField24Rows 12 := by decide +kernel
theorem LowerField24X13 : highNormUpperX LowerResult24 13 = LowerField24Rows 13 := by decide +kernel
theorem LowerField24X14 : highNormUpperX LowerResult24 14 = LowerField24Rows 14 := by decide +kernel
theorem LowerField24X15 : highNormUpperX LowerResult24 15 = LowerField24Rows 15 := by decide +kernel
theorem LowerField24X16 : highNormUpperX LowerResult24 16 = LowerField24Rows 16 := by decide +kernel
theorem LowerField24X17 : highNormUpperX LowerResult24 17 = LowerField24Rows 17 := by decide +kernel
theorem LowerField24X18 : highNormUpperX LowerResult24 18 = LowerField24Rows 18 := by decide +kernel
theorem LowerField24X19 : highNormUpperX LowerResult24 19 = LowerField24Rows 19 := by decide +kernel
theorem LowerField24_rows (x : Fin 20) : highNormUpperX LowerResult24 x = LowerField24Rows x := by
  fin_cases x
  · exact LowerField24X0
  · exact LowerField24X1
  · exact LowerField24X2
  · exact LowerField24X3
  · exact LowerField24X4
  · exact LowerField24X5
  · exact LowerField24X6
  · exact LowerField24X7
  · exact LowerField24X8
  · exact LowerField24X9
  · exact LowerField24X10
  · exact LowerField24X11
  · exact LowerField24X12
  · exact LowerField24X13
  · exact LowerField24X14
  · exact LowerField24X15
  · exact LowerField24X16
  · exact LowerField24X17
  · exact LowerField24X18
  · exact LowerField24X19
theorem LowerField24_bound : highNormUpper LowerResult24 ≤ 125728632793666853177123390614943 :=
  highNormUpper_le_of_rows LowerResult24 LowerField24Rows 125728632793666853177123390614943 LowerField24_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
