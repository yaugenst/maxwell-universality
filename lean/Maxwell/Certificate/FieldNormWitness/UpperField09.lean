import Maxwell.Certificate.ProjectionWitness.UpperResult9
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField09Rows : Fin 20 → ℤ := ![12922641853966709842599599948759, 23664209839698755853722754570463, 6796784803370813810584120664998, 672556090360016084074467129661, 341764223303401948978773431689, 71817999583234048433999742892, 69477152772760656493569455452, 17330876362468676009750322000, 18470150650363963307595912842, 7243468760491948713613250753, 7243468760491829462403041113, 18470150650363341768131238708, 17330876362468502086133329584, 69477152772761108454889839949, 71817999583233668827912486242, 341764223303407675390408592218, 672556090360018922080947515656, 6796784803370768530864072782548, 23664209839698628049440273058177, 12922641853966653562852510967510]
theorem UpperField09X0 : highNormUpperX UpperResult9 0 = UpperField09Rows 0 := by decide +kernel
theorem UpperField09X1 : highNormUpperX UpperResult9 1 = UpperField09Rows 1 := by decide +kernel
theorem UpperField09X2 : highNormUpperX UpperResult9 2 = UpperField09Rows 2 := by decide +kernel
theorem UpperField09X3 : highNormUpperX UpperResult9 3 = UpperField09Rows 3 := by decide +kernel
theorem UpperField09X4 : highNormUpperX UpperResult9 4 = UpperField09Rows 4 := by decide +kernel
theorem UpperField09X5 : highNormUpperX UpperResult9 5 = UpperField09Rows 5 := by decide +kernel
theorem UpperField09X6 : highNormUpperX UpperResult9 6 = UpperField09Rows 6 := by decide +kernel
theorem UpperField09X7 : highNormUpperX UpperResult9 7 = UpperField09Rows 7 := by decide +kernel
theorem UpperField09X8 : highNormUpperX UpperResult9 8 = UpperField09Rows 8 := by decide +kernel
theorem UpperField09X9 : highNormUpperX UpperResult9 9 = UpperField09Rows 9 := by decide +kernel
theorem UpperField09X10 : highNormUpperX UpperResult9 10 = UpperField09Rows 10 := by decide +kernel
theorem UpperField09X11 : highNormUpperX UpperResult9 11 = UpperField09Rows 11 := by decide +kernel
theorem UpperField09X12 : highNormUpperX UpperResult9 12 = UpperField09Rows 12 := by decide +kernel
theorem UpperField09X13 : highNormUpperX UpperResult9 13 = UpperField09Rows 13 := by decide +kernel
theorem UpperField09X14 : highNormUpperX UpperResult9 14 = UpperField09Rows 14 := by decide +kernel
theorem UpperField09X15 : highNormUpperX UpperResult9 15 = UpperField09Rows 15 := by decide +kernel
theorem UpperField09X16 : highNormUpperX UpperResult9 16 = UpperField09Rows 16 := by decide +kernel
theorem UpperField09X17 : highNormUpperX UpperResult9 17 = UpperField09Rows 17 := by decide +kernel
theorem UpperField09X18 : highNormUpperX UpperResult9 18 = UpperField09Rows 18 := by decide +kernel
theorem UpperField09X19 : highNormUpperX UpperResult9 19 = UpperField09Rows 19 := by decide +kernel
theorem UpperField09_rows (x : Fin 20) : highNormUpperX UpperResult9 x = UpperField09Rows x := by
  fin_cases x
  · exact UpperField09X0
  · exact UpperField09X1
  · exact UpperField09X2
  · exact UpperField09X3
  · exact UpperField09X4
  · exact UpperField09X5
  · exact UpperField09X6
  · exact UpperField09X7
  · exact UpperField09X8
  · exact UpperField09X9
  · exact UpperField09X10
  · exact UpperField09X11
  · exact UpperField09X12
  · exact UpperField09X13
  · exact UpperField09X14
  · exact UpperField09X15
  · exact UpperField09X16
  · exact UpperField09X17
  · exact UpperField09X18
  · exact UpperField09X19
theorem UpperField09_bound : highNormUpper UpperResult9 ≤ 89164592917657812024145927281214 :=
  highNormUpper_le_of_rows UpperResult9 UpperField09Rows 89164592917657812024145927281214 UpperField09_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
