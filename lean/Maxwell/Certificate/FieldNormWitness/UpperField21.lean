import Maxwell.Certificate.ProjectionWitness.UpperResult21
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField21Rows : Fin 20 → ℤ := ![19578617188580447686341899157301, 2617872127564144946183555080612, 24319807678377995328521321177749, 1301767808327493672775096284327, 305099745830853014759432526550, 203266254733856790119606365431, 32339340597502915106795598017, 44628754269751600566449276160, 7236129838257773330089165182, 12148568246376007200680249269, 12148568246375539199875190272, 7236129838257833462381495196, 44628754269749585702500951559, 32339340597501040310724451596, 203266254733849148472815864669, 305099745830830245491746042612, 1301767808327430403784204498243, 24319807678376034692165169454110, 2617872127563697399379514714501, 19578617188579042485922738291369]
theorem UpperField21X0 : highNormUpperX UpperResult21 0 = UpperField21Rows 0 := by decide +kernel
theorem UpperField21X1 : highNormUpperX UpperResult21 1 = UpperField21Rows 1 := by decide +kernel
theorem UpperField21X2 : highNormUpperX UpperResult21 2 = UpperField21Rows 2 := by decide +kernel
theorem UpperField21X3 : highNormUpperX UpperResult21 3 = UpperField21Rows 3 := by decide +kernel
theorem UpperField21X4 : highNormUpperX UpperResult21 4 = UpperField21Rows 4 := by decide +kernel
theorem UpperField21X5 : highNormUpperX UpperResult21 5 = UpperField21Rows 5 := by decide +kernel
theorem UpperField21X6 : highNormUpperX UpperResult21 6 = UpperField21Rows 6 := by decide +kernel
theorem UpperField21X7 : highNormUpperX UpperResult21 7 = UpperField21Rows 7 := by decide +kernel
theorem UpperField21X8 : highNormUpperX UpperResult21 8 = UpperField21Rows 8 := by decide +kernel
theorem UpperField21X9 : highNormUpperX UpperResult21 9 = UpperField21Rows 9 := by decide +kernel
theorem UpperField21X10 : highNormUpperX UpperResult21 10 = UpperField21Rows 10 := by decide +kernel
theorem UpperField21X11 : highNormUpperX UpperResult21 11 = UpperField21Rows 11 := by decide +kernel
theorem UpperField21X12 : highNormUpperX UpperResult21 12 = UpperField21Rows 12 := by decide +kernel
theorem UpperField21X13 : highNormUpperX UpperResult21 13 = UpperField21Rows 13 := by decide +kernel
theorem UpperField21X14 : highNormUpperX UpperResult21 14 = UpperField21Rows 14 := by decide +kernel
theorem UpperField21X15 : highNormUpperX UpperResult21 15 = UpperField21Rows 15 := by decide +kernel
theorem UpperField21X16 : highNormUpperX UpperResult21 16 = UpperField21Rows 16 := by decide +kernel
theorem UpperField21X17 : highNormUpperX UpperResult21 17 = UpperField21Rows 17 := by decide +kernel
theorem UpperField21X18 : highNormUpperX UpperResult21 18 = UpperField21Rows 18 := by decide +kernel
theorem UpperField21X19 : highNormUpperX UpperResult21 19 = UpperField21Rows 19 := by decide +kernel
theorem UpperField21_rows (x : Fin 20) : highNormUpperX UpperResult21 x = UpperField21Rows x := by
  fin_cases x
  · exact UpperField21X0
  · exact UpperField21X1
  · exact UpperField21X2
  · exact UpperField21X3
  · exact UpperField21X4
  · exact UpperField21X5
  · exact UpperField21X6
  · exact UpperField21X7
  · exact UpperField21X8
  · exact UpperField21X9
  · exact UpperField21X10
  · exact UpperField21X11
  · exact UpperField21X12
  · exact UpperField21X13
  · exact UpperField21X14
  · exact UpperField21X15
  · exact UpperField21X16
  · exact UpperField21X17
  · exact UpperField21X18
  · exact UpperField21X19
theorem UpperField21_bound : highNormUpper UpperResult21 ≤ 96845567192729448108796595834725 :=
  highNormUpper_le_of_rows UpperResult21 UpperField21Rows 96845567192729448108796595834725 UpperField21_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
