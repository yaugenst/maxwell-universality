import Maxwell.Certificate.ProjectionWitness.LowerResult9
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField09Rows : Fin 20 → ℤ := ![12716274881163530315608965916046, 25742208928018201467336978083880, 8273218975398087657911469421117, 756768406188994798130160005650, 407871963152207539352692122837, 82016979545061501203421177262, 79704840789190866493838926991, 19702076159756338379394165586, 20474206293136210991484039625, 8203744049079268584940757525, 8203744049079164999106136164, 20474206293136125331822139407, 19702076159756840158959552362, 79704840789192711183984253262, 82016979545059943755297005702, 407871963152221381612609086918, 756768406189020013175861852976, 8273218975398092741665068780039, 25742208928018025080688316209355, 12716274881163588993553112160517]
theorem LowerField09X0 : highNormUpperX LowerResult9 0 = LowerField09Rows 0 := by decide +kernel
theorem LowerField09X1 : highNormUpperX LowerResult9 1 = LowerField09Rows 1 := by decide +kernel
theorem LowerField09X2 : highNormUpperX LowerResult9 2 = LowerField09Rows 2 := by decide +kernel
theorem LowerField09X3 : highNormUpperX LowerResult9 3 = LowerField09Rows 3 := by decide +kernel
theorem LowerField09X4 : highNormUpperX LowerResult9 4 = LowerField09Rows 4 := by decide +kernel
theorem LowerField09X5 : highNormUpperX LowerResult9 5 = LowerField09Rows 5 := by decide +kernel
theorem LowerField09X6 : highNormUpperX LowerResult9 6 = LowerField09Rows 6 := by decide +kernel
theorem LowerField09X7 : highNormUpperX LowerResult9 7 = LowerField09Rows 7 := by decide +kernel
theorem LowerField09X8 : highNormUpperX LowerResult9 8 = LowerField09Rows 8 := by decide +kernel
theorem LowerField09X9 : highNormUpperX LowerResult9 9 = LowerField09Rows 9 := by decide +kernel
theorem LowerField09X10 : highNormUpperX LowerResult9 10 = LowerField09Rows 10 := by decide +kernel
theorem LowerField09X11 : highNormUpperX LowerResult9 11 = LowerField09Rows 11 := by decide +kernel
theorem LowerField09X12 : highNormUpperX LowerResult9 12 = LowerField09Rows 12 := by decide +kernel
theorem LowerField09X13 : highNormUpperX LowerResult9 13 = LowerField09Rows 13 := by decide +kernel
theorem LowerField09X14 : highNormUpperX LowerResult9 14 = LowerField09Rows 14 := by decide +kernel
theorem LowerField09X15 : highNormUpperX LowerResult9 15 = LowerField09Rows 15 := by decide +kernel
theorem LowerField09X16 : highNormUpperX LowerResult9 16 = LowerField09Rows 16 := by decide +kernel
theorem LowerField09X17 : highNormUpperX LowerResult9 17 = LowerField09Rows 17 := by decide +kernel
theorem LowerField09X18 : highNormUpperX LowerResult9 18 = LowerField09Rows 18 := by decide +kernel
theorem LowerField09X19 : highNormUpperX LowerResult9 19 = LowerField09Rows 19 := by decide +kernel
theorem LowerField09_rows (x : Fin 20) : highNormUpperX LowerResult9 x = LowerField09Rows x := by
  fin_cases x
  · exact LowerField09X0
  · exact LowerField09X1
  · exact LowerField09X2
  · exact LowerField09X3
  · exact LowerField09X4
  · exact LowerField09X5
  · exact LowerField09X6
  · exact LowerField09X7
  · exact LowerField09X8
  · exact LowerField09X9
  · exact LowerField09X10
  · exact LowerField09X11
  · exact LowerField09X12
  · exact LowerField09X13
  · exact LowerField09X14
  · exact LowerField09X15
  · exact LowerField09X16
  · exact LowerField09X17
  · exact LowerField09X18
  · exact LowerField09X19
theorem LowerField09_bound : highNormUpper LowerResult9 ≤ 96212890001514418960117481793221 :=
  highNormUpper_le_of_rows LowerResult9 LowerField09Rows 96212890001514418960117481793221 LowerField09_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
