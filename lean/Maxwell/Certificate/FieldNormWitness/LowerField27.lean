import Maxwell.Certificate.ProjectionWitness.LowerResult27
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField27Rows : Fin 20 → ℤ := ![15296638008579170482337119160433, 3505110352786901455354680877178, 10571953384589818664969287313120, 1311561776740782150693382713391, 159420337457164378225358975167, 131885739855364069484283105410, 36277845504128304036087862425, 29259109331706128532694799557, 10008792913276905984970283949, 11891830325784221723451955708, 11891830325784044402370670987, 10008792913276837086611853368, 29259109331706812123978722651, 36277845504128647414973767230, 131885739855366297608739944824, 159420337457166090087729079376, 1311561776740806544895996267937, 10571953384590022862072888296383, 3505110352786931210540114356399, 15296638008579074822213489923772]
theorem LowerField27X0 : highNormUpperX LowerResult27 0 = LowerField27Rows 0 := by decide +kernel
theorem LowerField27X1 : highNormUpperX LowerResult27 1 = LowerField27Rows 1 := by decide +kernel
theorem LowerField27X2 : highNormUpperX LowerResult27 2 = LowerField27Rows 2 := by decide +kernel
theorem LowerField27X3 : highNormUpperX LowerResult27 3 = LowerField27Rows 3 := by decide +kernel
theorem LowerField27X4 : highNormUpperX LowerResult27 4 = LowerField27Rows 4 := by decide +kernel
theorem LowerField27X5 : highNormUpperX LowerResult27 5 = LowerField27Rows 5 := by decide +kernel
theorem LowerField27X6 : highNormUpperX LowerResult27 6 = LowerField27Rows 6 := by decide +kernel
theorem LowerField27X7 : highNormUpperX LowerResult27 7 = LowerField27Rows 7 := by decide +kernel
theorem LowerField27X8 : highNormUpperX LowerResult27 8 = LowerField27Rows 8 := by decide +kernel
theorem LowerField27X9 : highNormUpperX LowerResult27 9 = LowerField27Rows 9 := by decide +kernel
theorem LowerField27X10 : highNormUpperX LowerResult27 10 = LowerField27Rows 10 := by decide +kernel
theorem LowerField27X11 : highNormUpperX LowerResult27 11 = LowerField27Rows 11 := by decide +kernel
theorem LowerField27X12 : highNormUpperX LowerResult27 12 = LowerField27Rows 12 := by decide +kernel
theorem LowerField27X13 : highNormUpperX LowerResult27 13 = LowerField27Rows 13 := by decide +kernel
theorem LowerField27X14 : highNormUpperX LowerResult27 14 = LowerField27Rows 14 := by decide +kernel
theorem LowerField27X15 : highNormUpperX LowerResult27 15 = LowerField27Rows 15 := by decide +kernel
theorem LowerField27X16 : highNormUpperX LowerResult27 16 = LowerField27Rows 16 := by decide +kernel
theorem LowerField27X17 : highNormUpperX LowerResult27 17 = LowerField27Rows 17 := by decide +kernel
theorem LowerField27X18 : highNormUpperX LowerResult27 18 = LowerField27Rows 18 := by decide +kernel
theorem LowerField27X19 : highNormUpperX LowerResult27 19 = LowerField27Rows 19 := by decide +kernel
theorem LowerField27_rows (x : Fin 20) : highNormUpperX LowerResult27 x = LowerField27Rows x := by
  fin_cases x
  · exact LowerField27X0
  · exact LowerField27X1
  · exact LowerField27X2
  · exact LowerField27X3
  · exact LowerField27X4
  · exact LowerField27X5
  · exact LowerField27X6
  · exact LowerField27X7
  · exact LowerField27X8
  · exact LowerField27X9
  · exact LowerField27X10
  · exact LowerField27X11
  · exact LowerField27X12
  · exact LowerField27X13
  · exact LowerField27X14
  · exact LowerField27X15
  · exact LowerField27X16
  · exact LowerField27X17
  · exact LowerField27X18
  · exact LowerField27X19
theorem LowerField27_bound : highNormUpper LowerResult27 ≤ 62128014356168360929788209929265 :=
  highNormUpper_le_of_rows LowerResult27 LowerField27Rows 62128014356168360929788209929265 LowerField27_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
