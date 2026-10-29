import Maxwell.Certificate.ProjectionWitness.UpperResult8
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField08Rows : Fin 20 → ℤ := ![13518674271448642855395648100500, 7167192410834751333011809033084, 22127715729670054612334394391013, 1124250201968058493486531567911, 383844392804532812055994037595, 161624639907126262928952112983, 50323415467704438173453314603, 30150352237618396482077805889, 11615704872431559463214796797, 6905339618036345262566078938, 6905339618036314529816835703, 11615704872431359843599913084, 30150352237619006381533532600, 50323415467704470651876295019, 161624639907125097558286805789, 383844392804533757818823454896, 1124250201968050713307509101195, 22127715729670093063834945710565, 7167192410834805735082902792818, 13518674271448597953339263428300]
theorem UpperField08X0 : highNormUpperX UpperResult8 0 = UpperField08Rows 0 := by decide +kernel
theorem UpperField08X1 : highNormUpperX UpperResult8 1 = UpperField08Rows 1 := by decide +kernel
theorem UpperField08X2 : highNormUpperX UpperResult8 2 = UpperField08Rows 2 := by decide +kernel
theorem UpperField08X3 : highNormUpperX UpperResult8 3 = UpperField08Rows 3 := by decide +kernel
theorem UpperField08X4 : highNormUpperX UpperResult8 4 = UpperField08Rows 4 := by decide +kernel
theorem UpperField08X5 : highNormUpperX UpperResult8 5 = UpperField08Rows 5 := by decide +kernel
theorem UpperField08X6 : highNormUpperX UpperResult8 6 = UpperField08Rows 6 := by decide +kernel
theorem UpperField08X7 : highNormUpperX UpperResult8 7 = UpperField08Rows 7 := by decide +kernel
theorem UpperField08X8 : highNormUpperX UpperResult8 8 = UpperField08Rows 8 := by decide +kernel
theorem UpperField08X9 : highNormUpperX UpperResult8 9 = UpperField08Rows 9 := by decide +kernel
theorem UpperField08X10 : highNormUpperX UpperResult8 10 = UpperField08Rows 10 := by decide +kernel
theorem UpperField08X11 : highNormUpperX UpperResult8 11 = UpperField08Rows 11 := by decide +kernel
theorem UpperField08X12 : highNormUpperX UpperResult8 12 = UpperField08Rows 12 := by decide +kernel
theorem UpperField08X13 : highNormUpperX UpperResult8 13 = UpperField08Rows 13 := by decide +kernel
theorem UpperField08X14 : highNormUpperX UpperResult8 14 = UpperField08Rows 14 := by decide +kernel
theorem UpperField08X15 : highNormUpperX UpperResult8 15 = UpperField08Rows 15 := by decide +kernel
theorem UpperField08X16 : highNormUpperX UpperResult8 16 = UpperField08Rows 16 := by decide +kernel
theorem UpperField08X17 : highNormUpperX UpperResult8 17 = UpperField08Rows 17 := by decide +kernel
theorem UpperField08X18 : highNormUpperX UpperResult8 18 = UpperField08Rows 18 := by decide +kernel
theorem UpperField08X19 : highNormUpperX UpperResult8 19 = UpperField08Rows 19 := by decide +kernel
theorem UpperField08_rows (x : Fin 20) : highNormUpperX UpperResult8 x = UpperField08Rows x := by
  fin_cases x
  · exact UpperField08X0
  · exact UpperField08X1
  · exact UpperField08X2
  · exact UpperField08X3
  · exact UpperField08X4
  · exact UpperField08X5
  · exact UpperField08X6
  · exact UpperField08X7
  · exact UpperField08X8
  · exact UpperField08X9
  · exact UpperField08X10
  · exact UpperField08X11
  · exact UpperField08X12
  · exact UpperField08X13
  · exact UpperField08X14
  · exact UpperField08X15
  · exact UpperField08X16
  · exact UpperField08X17
  · exact UpperField08X18
  · exact UpperField08X19
theorem UpperField08_bound : highNormUpper UpperResult8 ≤ 89164592917657954580943199109282 :=
  highNormUpper_le_of_rows UpperResult8 UpperField08Rows 89164592917657954580943199109282 UpperField08_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
