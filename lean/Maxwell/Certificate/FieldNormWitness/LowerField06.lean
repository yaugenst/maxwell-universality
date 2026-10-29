import Maxwell.Certificate.ProjectionWitness.LowerResult6
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField06Rows : Fin 20 → ℤ := ![35293689900080937770812642243787, 24527891824307997225707328529370, 2838338399160072602786579194471, 494100454974250104340686319972, 184587302768448399351977847002, 64347150030470912610468109671, 24074050096510995474441524932, 20577249281732148020728612899, 9696012614525794787928891429, 2998264340724291197415406218, 2998264340724343720894668881, 9696012614524877336746126168, 20577249281732459818638223946, 24074050096510879677319463550, 64347150030470384082150611784, 184587302768451439458202867345, 494100454974280082018746971116, 2838338399159905853916256608349, 24527891824307918445478207579320, 35293689900081062904929689958471]
theorem LowerField06X0 : highNormUpperX LowerResult6 0 = LowerField06Rows 0 := by decide +kernel
theorem LowerField06X1 : highNormUpperX LowerResult6 1 = LowerField06Rows 1 := by decide +kernel
theorem LowerField06X2 : highNormUpperX LowerResult6 2 = LowerField06Rows 2 := by decide +kernel
theorem LowerField06X3 : highNormUpperX LowerResult6 3 = LowerField06Rows 3 := by decide +kernel
theorem LowerField06X4 : highNormUpperX LowerResult6 4 = LowerField06Rows 4 := by decide +kernel
theorem LowerField06X5 : highNormUpperX LowerResult6 5 = LowerField06Rows 5 := by decide +kernel
theorem LowerField06X6 : highNormUpperX LowerResult6 6 = LowerField06Rows 6 := by decide +kernel
theorem LowerField06X7 : highNormUpperX LowerResult6 7 = LowerField06Rows 7 := by decide +kernel
theorem LowerField06X8 : highNormUpperX LowerResult6 8 = LowerField06Rows 8 := by decide +kernel
theorem LowerField06X9 : highNormUpperX LowerResult6 9 = LowerField06Rows 9 := by decide +kernel
theorem LowerField06X10 : highNormUpperX LowerResult6 10 = LowerField06Rows 10 := by decide +kernel
theorem LowerField06X11 : highNormUpperX LowerResult6 11 = LowerField06Rows 11 := by decide +kernel
theorem LowerField06X12 : highNormUpperX LowerResult6 12 = LowerField06Rows 12 := by decide +kernel
theorem LowerField06X13 : highNormUpperX LowerResult6 13 = LowerField06Rows 13 := by decide +kernel
theorem LowerField06X14 : highNormUpperX LowerResult6 14 = LowerField06Rows 14 := by decide +kernel
theorem LowerField06X15 : highNormUpperX LowerResult6 15 = LowerField06Rows 15 := by decide +kernel
theorem LowerField06X16 : highNormUpperX LowerResult6 16 = LowerField06Rows 16 := by decide +kernel
theorem LowerField06X17 : highNormUpperX LowerResult6 17 = LowerField06Rows 17 := by decide +kernel
theorem LowerField06X18 : highNormUpperX LowerResult6 18 = LowerField06Rows 18 := by decide +kernel
theorem LowerField06X19 : highNormUpperX LowerResult6 19 = LowerField06Rows 19 := by decide +kernel
theorem LowerField06_rows (x : Fin 20) : highNormUpperX LowerResult6 x = LowerField06Rows x := by
  fin_cases x
  · exact LowerField06X0
  · exact LowerField06X1
  · exact LowerField06X2
  · exact LowerField06X3
  · exact LowerField06X4
  · exact LowerField06X5
  · exact LowerField06X6
  · exact LowerField06X7
  · exact LowerField06X8
  · exact LowerField06X9
  · exact LowerField06X10
  · exact LowerField06X11
  · exact LowerField06X12
  · exact LowerField06X13
  · exact LowerField06X14
  · exact LowerField06X15
  · exact LowerField06X16
  · exact LowerField06X17
  · exact LowerField06X18
  · exact LowerField06X19
theorem LowerField06_bound : highNormUpper LowerResult6 ≤ 126920601215311251915527049758681 :=
  highNormUpper_le_of_rows LowerResult6 LowerField06Rows 126920601215311251915527049758681 LowerField06_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
