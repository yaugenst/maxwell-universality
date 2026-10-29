import Maxwell.Certificate.ProjectionWitness.LowerResult16
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField16Rows : Fin 20 → ℤ := ![14082641069847426867197443463199, 14555732587493385448767921652328, 17750517566915840648518500255531, 1186451239585291369817523172797, 412205598477089148436240905990, 173174120706862701101579291879, 63261803136732151131819342075, 35849810916585137665145095218, 17507123952359799901997269998, 10272852661344791034293639148, 10272852661344649415272190575, 17507123952359672383862994088, 35849810916584852489385740380, 63261803136731103876699342744, 173174120706862319936525540499, 412205598477082874959387463837, 1186451239585293276825894366109, 17750517566915626419887460073778, 14555732587493435740165954400316, 14082641069847278802356541894134]
theorem LowerField16X0 : highNormUpperX LowerResult16 0 = LowerField16Rows 0 := by decide +kernel
theorem LowerField16X1 : highNormUpperX LowerResult16 1 = LowerField16Rows 1 := by decide +kernel
theorem LowerField16X2 : highNormUpperX LowerResult16 2 = LowerField16Rows 2 := by decide +kernel
theorem LowerField16X3 : highNormUpperX LowerResult16 3 = LowerField16Rows 3 := by decide +kernel
theorem LowerField16X4 : highNormUpperX LowerResult16 4 = LowerField16Rows 4 := by decide +kernel
theorem LowerField16X5 : highNormUpperX LowerResult16 5 = LowerField16Rows 5 := by decide +kernel
theorem LowerField16X6 : highNormUpperX LowerResult16 6 = LowerField16Rows 6 := by decide +kernel
theorem LowerField16X7 : highNormUpperX LowerResult16 7 = LowerField16Rows 7 := by decide +kernel
theorem LowerField16X8 : highNormUpperX LowerResult16 8 = LowerField16Rows 8 := by decide +kernel
theorem LowerField16X9 : highNormUpperX LowerResult16 9 = LowerField16Rows 9 := by decide +kernel
theorem LowerField16X10 : highNormUpperX LowerResult16 10 = LowerField16Rows 10 := by decide +kernel
theorem LowerField16X11 : highNormUpperX LowerResult16 11 = LowerField16Rows 11 := by decide +kernel
theorem LowerField16X12 : highNormUpperX LowerResult16 12 = LowerField16Rows 12 := by decide +kernel
theorem LowerField16X13 : highNormUpperX LowerResult16 13 = LowerField16Rows 13 := by decide +kernel
theorem LowerField16X14 : highNormUpperX LowerResult16 14 = LowerField16Rows 14 := by decide +kernel
theorem LowerField16X15 : highNormUpperX LowerResult16 15 = LowerField16Rows 15 := by decide +kernel
theorem LowerField16X16 : highNormUpperX LowerResult16 16 = LowerField16Rows 16 := by decide +kernel
theorem LowerField16X17 : highNormUpperX LowerResult16 17 = LowerField16Rows 17 := by decide +kernel
theorem LowerField16X18 : highNormUpperX LowerResult16 18 = LowerField16Rows 18 := by decide +kernel
theorem LowerField16X19 : highNormUpperX LowerResult16 19 = LowerField16Rows 19 := by decide +kernel
theorem LowerField16_rows (x : Fin 20) : highNormUpperX LowerResult16 x = LowerField16Rows x := by
  fin_cases x
  · exact LowerField16X0
  · exact LowerField16X1
  · exact LowerField16X2
  · exact LowerField16X3
  · exact LowerField16X4
  · exact LowerField16X5
  · exact LowerField16X6
  · exact LowerField16X7
  · exact LowerField16X8
  · exact LowerField16X9
  · exact LowerField16X10
  · exact LowerField16X11
  · exact LowerField16X12
  · exact LowerField16X13
  · exact LowerField16X14
  · exact LowerField16X15
  · exact LowerField16X16
  · exact LowerField16X17
  · exact LowerField16X18
  · exact LowerField16X19
theorem LowerField16_bound : highNormUpper LowerResult16 ≤ 96575227547385517775869448094623 :=
  highNormUpper_le_of_rows LowerResult16 LowerField16Rows 96575227547385517775869448094623 LowerField16_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
