import Maxwell.Certificate.ProjectionWitness.UpperResult14
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField14Rows : Fin 20 → ℤ := ![5088301888061856849611246230646, 9795768565819638524956275582584, 22808380916060780163202146705124, 745375166685684896405928615133, 346589033669003219177650538126, 102430281137894933576905514655, 41007026014008654893372495622, 22705496266953658562744013733, 5619053706985225394611652503, 6078271445535046739940989615, 6078271445535078681084889434, 5619053706985360956168761756, 22705496266953678828867574999, 41007026014008532517299339596, 102430281137894203341171159621, 346589033669003208271080253081, 745375166685690310441895991868, 22808380916060684579875847728510, 9795768565819673162615875013557, 5088301888061858598713057096554]
theorem UpperField14X0 : highNormUpperX UpperResult14 0 = UpperField14Rows 0 := by decide +kernel
theorem UpperField14X1 : highNormUpperX UpperResult14 1 = UpperField14Rows 1 := by decide +kernel
theorem UpperField14X2 : highNormUpperX UpperResult14 2 = UpperField14Rows 2 := by decide +kernel
theorem UpperField14X3 : highNormUpperX UpperResult14 3 = UpperField14Rows 3 := by decide +kernel
theorem UpperField14X4 : highNormUpperX UpperResult14 4 = UpperField14Rows 4 := by decide +kernel
theorem UpperField14X5 : highNormUpperX UpperResult14 5 = UpperField14Rows 5 := by decide +kernel
theorem UpperField14X6 : highNormUpperX UpperResult14 6 = UpperField14Rows 6 := by decide +kernel
theorem UpperField14X7 : highNormUpperX UpperResult14 7 = UpperField14Rows 7 := by decide +kernel
theorem UpperField14X8 : highNormUpperX UpperResult14 8 = UpperField14Rows 8 := by decide +kernel
theorem UpperField14X9 : highNormUpperX UpperResult14 9 = UpperField14Rows 9 := by decide +kernel
theorem UpperField14X10 : highNormUpperX UpperResult14 10 = UpperField14Rows 10 := by decide +kernel
theorem UpperField14X11 : highNormUpperX UpperResult14 11 = UpperField14Rows 11 := by decide +kernel
theorem UpperField14X12 : highNormUpperX UpperResult14 12 = UpperField14Rows 12 := by decide +kernel
theorem UpperField14X13 : highNormUpperX UpperResult14 13 = UpperField14Rows 13 := by decide +kernel
theorem UpperField14X14 : highNormUpperX UpperResult14 14 = UpperField14Rows 14 := by decide +kernel
theorem UpperField14X15 : highNormUpperX UpperResult14 15 = UpperField14Rows 15 := by decide +kernel
theorem UpperField14X16 : highNormUpperX UpperResult14 16 = UpperField14Rows 16 := by decide +kernel
theorem UpperField14X17 : highNormUpperX UpperResult14 17 = UpperField14Rows 17 := by decide +kernel
theorem UpperField14X18 : highNormUpperX UpperResult14 18 = UpperField14Rows 18 := by decide +kernel
theorem UpperField14X19 : highNormUpperX UpperResult14 19 = UpperField14Rows 19 := by decide +kernel
theorem UpperField14_rows (x : Fin 20) : highNormUpperX UpperResult14 x = UpperField14Rows x := by
  fin_cases x
  · exact UpperField14X0
  · exact UpperField14X1
  · exact UpperField14X2
  · exact UpperField14X3
  · exact UpperField14X4
  · exact UpperField14X5
  · exact UpperField14X6
  · exact UpperField14X7
  · exact UpperField14X8
  · exact UpperField14X9
  · exact UpperField14X10
  · exact UpperField14X11
  · exact UpperField14X12
  · exact UpperField14X13
  · exact UpperField14X14
  · exact UpperField14X15
  · exact UpperField14X16
  · exact UpperField14X17
  · exact UpperField14X18
  · exact UpperField14X19
theorem UpperField14_bound : highNormUpper UpperResult14 ≤ 77924511397736627886763170146717 :=
  highNormUpper_le_of_rows UpperResult14 UpperField14Rows 77924511397736627886763170146717 UpperField14_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
