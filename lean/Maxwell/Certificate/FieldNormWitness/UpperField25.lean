import Maxwell.Certificate.ProjectionWitness.UpperResult25
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField25Rows : Fin 20 → ℤ := ![15753223405568886451313711231726, 2415494098015841986275858936934, 11119287278674738915985303527622, 771430148119100528714241618865, 128609208165235578505841745319, 98964291899344202998828048293, 20728742953883813175530526058, 21536282960734543201380356932, 6151567662985464405537381376, 7316021643614385805761113300, 7316021643614668988143523964, 6151567662984878670388022732, 21536282960735514700605926519, 20728742953882088248980349123, 98964291899346610842716136503, 128609208165229416445692602336, 771430148119103794811985759752, 11119287278674820118343612987611, 2415494098015703317993530253246, 15753223405568784623634241753946]
theorem UpperField25X0 : highNormUpperX UpperResult25 0 = UpperField25Rows 0 := by decide +kernel
theorem UpperField25X1 : highNormUpperX UpperResult25 1 = UpperField25Rows 1 := by decide +kernel
theorem UpperField25X2 : highNormUpperX UpperResult25 2 = UpperField25Rows 2 := by decide +kernel
theorem UpperField25X3 : highNormUpperX UpperResult25 3 = UpperField25Rows 3 := by decide +kernel
theorem UpperField25X4 : highNormUpperX UpperResult25 4 = UpperField25Rows 4 := by decide +kernel
theorem UpperField25X5 : highNormUpperX UpperResult25 5 = UpperField25Rows 5 := by decide +kernel
theorem UpperField25X6 : highNormUpperX UpperResult25 6 = UpperField25Rows 6 := by decide +kernel
theorem UpperField25X7 : highNormUpperX UpperResult25 7 = UpperField25Rows 7 := by decide +kernel
theorem UpperField25X8 : highNormUpperX UpperResult25 8 = UpperField25Rows 8 := by decide +kernel
theorem UpperField25X9 : highNormUpperX UpperResult25 9 = UpperField25Rows 9 := by decide +kernel
theorem UpperField25X10 : highNormUpperX UpperResult25 10 = UpperField25Rows 10 := by decide +kernel
theorem UpperField25X11 : highNormUpperX UpperResult25 11 = UpperField25Rows 11 := by decide +kernel
theorem UpperField25X12 : highNormUpperX UpperResult25 12 = UpperField25Rows 12 := by decide +kernel
theorem UpperField25X13 : highNormUpperX UpperResult25 13 = UpperField25Rows 13 := by decide +kernel
theorem UpperField25X14 : highNormUpperX UpperResult25 14 = UpperField25Rows 14 := by decide +kernel
theorem UpperField25X15 : highNormUpperX UpperResult25 15 = UpperField25Rows 15 := by decide +kernel
theorem UpperField25X16 : highNormUpperX UpperResult25 16 = UpperField25Rows 16 := by decide +kernel
theorem UpperField25X17 : highNormUpperX UpperResult25 17 = UpperField25Rows 17 := by decide +kernel
theorem UpperField25X18 : highNormUpperX UpperResult25 18 = UpperField25Rows 18 := by decide +kernel
theorem UpperField25X19 : highNormUpperX UpperResult25 19 = UpperField25Rows 19 := by decide +kernel
theorem UpperField25_rows (x : Fin 20) : highNormUpperX UpperResult25 x = UpperField25Rows x := by
  fin_cases x
  · exact UpperField25X0
  · exact UpperField25X1
  · exact UpperField25X2
  · exact UpperField25X3
  · exact UpperField25X4
  · exact UpperField25X5
  · exact UpperField25X6
  · exact UpperField25X7
  · exact UpperField25X8
  · exact UpperField25X9
  · exact UpperField25X10
  · exact UpperField25X11
  · exact UpperField25X12
  · exact UpperField25X13
  · exact UpperField25X14
  · exact UpperField25X15
  · exact UpperField25X16
  · exact UpperField25X17
  · exact UpperField25X18
  · exact UpperField25X19
theorem UpperField25_bound : highNormUpper UpperResult25 ≤ 60685482091328570903061891802157 :=
  highNormUpper_le_of_rows UpperResult25 UpperField25Rows 60685482091328570903061891802157 UpperField25_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
