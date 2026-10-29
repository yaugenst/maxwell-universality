import Maxwell.Certificate.ProjectionWitness.LowerResult25
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField25Rows : Fin 20 → ℤ := ![14441867297465319258065525053550, 5352095243610467546686873578198, 13944854257882407678132671927466, 1422550289478277063780868157155, 234834271638858390593880001506, 134751282355150985386498125889, 50978308712666022138248981087, 30762118672370721019157840288, 16834586259354467664624176977, 13884786490007050139820852608, 13884786490006959180566197103, 16834586259354066610793367910, 30762118672370645553743070770, 50978308712665165145328786714, 134751282355152052428871413673, 234834271638856973352258477787, 1422550289478279398426817935167, 13944854257882473372939595823216, 5352095243610419628276616324032, 14441867297465321712760666680317]
theorem LowerField25X0 : highNormUpperX LowerResult25 0 = LowerField25Rows 0 := by decide +kernel
theorem LowerField25X1 : highNormUpperX LowerResult25 1 = LowerField25Rows 1 := by decide +kernel
theorem LowerField25X2 : highNormUpperX LowerResult25 2 = LowerField25Rows 2 := by decide +kernel
theorem LowerField25X3 : highNormUpperX LowerResult25 3 = LowerField25Rows 3 := by decide +kernel
theorem LowerField25X4 : highNormUpperX LowerResult25 4 = LowerField25Rows 4 := by decide +kernel
theorem LowerField25X5 : highNormUpperX LowerResult25 5 = LowerField25Rows 5 := by decide +kernel
theorem LowerField25X6 : highNormUpperX LowerResult25 6 = LowerField25Rows 6 := by decide +kernel
theorem LowerField25X7 : highNormUpperX LowerResult25 7 = LowerField25Rows 7 := by decide +kernel
theorem LowerField25X8 : highNormUpperX LowerResult25 8 = LowerField25Rows 8 := by decide +kernel
theorem LowerField25X9 : highNormUpperX LowerResult25 9 = LowerField25Rows 9 := by decide +kernel
theorem LowerField25X10 : highNormUpperX LowerResult25 10 = LowerField25Rows 10 := by decide +kernel
theorem LowerField25X11 : highNormUpperX LowerResult25 11 = LowerField25Rows 11 := by decide +kernel
theorem LowerField25X12 : highNormUpperX LowerResult25 12 = LowerField25Rows 12 := by decide +kernel
theorem LowerField25X13 : highNormUpperX LowerResult25 13 = LowerField25Rows 13 := by decide +kernel
theorem LowerField25X14 : highNormUpperX LowerResult25 14 = LowerField25Rows 14 := by decide +kernel
theorem LowerField25X15 : highNormUpperX LowerResult25 15 = LowerField25Rows 15 := by decide +kernel
theorem LowerField25X16 : highNormUpperX LowerResult25 16 = LowerField25Rows 16 := by decide +kernel
theorem LowerField25X17 : highNormUpperX LowerResult25 17 = LowerField25Rows 17 := by decide +kernel
theorem LowerField25X18 : highNormUpperX LowerResult25 18 = LowerField25Rows 18 := by decide +kernel
theorem LowerField25X19 : highNormUpperX LowerResult25 19 = LowerField25Rows 19 := by decide +kernel
theorem LowerField25_rows (x : Fin 20) : highNormUpperX LowerResult25 x = LowerField25Rows x := by
  fin_cases x
  · exact LowerField25X0
  · exact LowerField25X1
  · exact LowerField25X2
  · exact LowerField25X3
  · exact LowerField25X4
  · exact LowerField25X5
  · exact LowerField25X6
  · exact LowerField25X7
  · exact LowerField25X8
  · exact LowerField25X9
  · exact LowerField25X10
  · exact LowerField25X11
  · exact LowerField25X12
  · exact LowerField25X13
  · exact LowerField25X14
  · exact LowerField25X15
  · exact LowerField25X16
  · exact LowerField25X17
  · exact LowerField25X18
  · exact LowerField25X19
theorem LowerField25_bound : highNormUpper LowerResult25 ≤ 71286824885129779158283426771413 :=
  highNormUpper_le_of_rows LowerResult25 LowerField25Rows 71286824885129779158283426771413 LowerField25_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
