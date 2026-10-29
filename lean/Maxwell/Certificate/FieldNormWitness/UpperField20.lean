import Maxwell.Certificate.ProjectionWitness.UpperResult20
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField20Rows : Fin 20 → ℤ := ![23810006846508495891473100903902, 11396270676819683217844382698620, 12059024435945800347188119665142, 760378056134948755558415910470, 243730023677090974543778218238, 87037772086830989423655427624, 31771769144179291034129562301, 21278742336256329097122755722, 6502722459663053497323507797, 6782551251609499911025691995, 6782551251609407245086713951, 6502722459662895569735709527, 21278742336255152410398339771, 31771769144178484568971370638, 87037772086825879868207983101, 243730023677084059974649472292, 760378056134907244856700515689, 12059024435945264038946655589298, 11396270676819478375179840031380, 23810006846509619563296093252861]
theorem UpperField20X0 : highNormUpperX UpperResult20 0 = UpperField20Rows 0 := by decide +kernel
theorem UpperField20X1 : highNormUpperX UpperResult20 1 = UpperField20Rows 1 := by decide +kernel
theorem UpperField20X2 : highNormUpperX UpperResult20 2 = UpperField20Rows 2 := by decide +kernel
theorem UpperField20X3 : highNormUpperX UpperResult20 3 = UpperField20Rows 3 := by decide +kernel
theorem UpperField20X4 : highNormUpperX UpperResult20 4 = UpperField20Rows 4 := by decide +kernel
theorem UpperField20X5 : highNormUpperX UpperResult20 5 = UpperField20Rows 5 := by decide +kernel
theorem UpperField20X6 : highNormUpperX UpperResult20 6 = UpperField20Rows 6 := by decide +kernel
theorem UpperField20X7 : highNormUpperX UpperResult20 7 = UpperField20Rows 7 := by decide +kernel
theorem UpperField20X8 : highNormUpperX UpperResult20 8 = UpperField20Rows 8 := by decide +kernel
theorem UpperField20X9 : highNormUpperX UpperResult20 9 = UpperField20Rows 9 := by decide +kernel
theorem UpperField20X10 : highNormUpperX UpperResult20 10 = UpperField20Rows 10 := by decide +kernel
theorem UpperField20X11 : highNormUpperX UpperResult20 11 = UpperField20Rows 11 := by decide +kernel
theorem UpperField20X12 : highNormUpperX UpperResult20 12 = UpperField20Rows 12 := by decide +kernel
theorem UpperField20X13 : highNormUpperX UpperResult20 13 = UpperField20Rows 13 := by decide +kernel
theorem UpperField20X14 : highNormUpperX UpperResult20 14 = UpperField20Rows 14 := by decide +kernel
theorem UpperField20X15 : highNormUpperX UpperResult20 15 = UpperField20Rows 15 := by decide +kernel
theorem UpperField20X16 : highNormUpperX UpperResult20 16 = UpperField20Rows 16 := by decide +kernel
theorem UpperField20X17 : highNormUpperX UpperResult20 17 = UpperField20Rows 17 := by decide +kernel
theorem UpperField20X18 : highNormUpperX UpperResult20 18 = UpperField20Rows 18 := by decide +kernel
theorem UpperField20X19 : highNormUpperX UpperResult20 19 = UpperField20Rows 19 := by decide +kernel
theorem UpperField20_rows (x : Fin 20) : highNormUpperX UpperResult20 x = UpperField20Rows x := by
  fin_cases x
  · exact UpperField20X0
  · exact UpperField20X1
  · exact UpperField20X2
  · exact UpperField20X3
  · exact UpperField20X4
  · exact UpperField20X5
  · exact UpperField20X6
  · exact UpperField20X7
  · exact UpperField20X8
  · exact UpperField20X9
  · exact UpperField20X10
  · exact UpperField20X11
  · exact UpperField20X12
  · exact UpperField20X13
  · exact UpperField20X14
  · exact UpperField20X15
  · exact UpperField20X16
  · exact UpperField20X17
  · exact UpperField20X18
  · exact UpperField20X19
theorem UpperField20_bound : highNormUpper UpperResult20 ≤ 96845567192729443451487393320319 :=
  highNormUpper_le_of_rows UpperResult20 UpperField20Rows 96845567192729443451487393320319 UpperField20_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
