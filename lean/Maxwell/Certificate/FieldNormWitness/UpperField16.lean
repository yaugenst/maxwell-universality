import Maxwell.Certificate.ProjectionWitness.UpperResult16
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField16Rows : Fin 20 → ℤ := ![16551587860375212289354192060102, 10398613182972298284216705348553, 18384838124819516782677029618097, 1290233256011984710417507038448, 292334179382464248499673566997, 227443963027213367889048353068, 32550686178974898448901809861, 41318773896678170876094157203, 6859781441852699953538509768, 11614496491824258829991904556, 11614496491824405873857202127, 6859781441852603085282671962, 41318773896677599094254154509, 32550686178975202242941713533, 227443963027211612165130075229, 292334179382463456063893306734, 1290233256011977402825281105539, 18384838124819397439872615371378, 10398613182972180212221362259753, 16551587860375164281677340504715]
theorem UpperField16X0 : highNormUpperX UpperResult16 0 = UpperField16Rows 0 := by decide +kernel
theorem UpperField16X1 : highNormUpperX UpperResult16 1 = UpperField16Rows 1 := by decide +kernel
theorem UpperField16X2 : highNormUpperX UpperResult16 2 = UpperField16Rows 2 := by decide +kernel
theorem UpperField16X3 : highNormUpperX UpperResult16 3 = UpperField16Rows 3 := by decide +kernel
theorem UpperField16X4 : highNormUpperX UpperResult16 4 = UpperField16Rows 4 := by decide +kernel
theorem UpperField16X5 : highNormUpperX UpperResult16 5 = UpperField16Rows 5 := by decide +kernel
theorem UpperField16X6 : highNormUpperX UpperResult16 6 = UpperField16Rows 6 := by decide +kernel
theorem UpperField16X7 : highNormUpperX UpperResult16 7 = UpperField16Rows 7 := by decide +kernel
theorem UpperField16X8 : highNormUpperX UpperResult16 8 = UpperField16Rows 8 := by decide +kernel
theorem UpperField16X9 : highNormUpperX UpperResult16 9 = UpperField16Rows 9 := by decide +kernel
theorem UpperField16X10 : highNormUpperX UpperResult16 10 = UpperField16Rows 10 := by decide +kernel
theorem UpperField16X11 : highNormUpperX UpperResult16 11 = UpperField16Rows 11 := by decide +kernel
theorem UpperField16X12 : highNormUpperX UpperResult16 12 = UpperField16Rows 12 := by decide +kernel
theorem UpperField16X13 : highNormUpperX UpperResult16 13 = UpperField16Rows 13 := by decide +kernel
theorem UpperField16X14 : highNormUpperX UpperResult16 14 = UpperField16Rows 14 := by decide +kernel
theorem UpperField16X15 : highNormUpperX UpperResult16 15 = UpperField16Rows 15 := by decide +kernel
theorem UpperField16X16 : highNormUpperX UpperResult16 16 = UpperField16Rows 16 := by decide +kernel
theorem UpperField16X17 : highNormUpperX UpperResult16 17 = UpperField16Rows 17 := by decide +kernel
theorem UpperField16X18 : highNormUpperX UpperResult16 18 = UpperField16Rows 18 := by decide +kernel
theorem UpperField16X19 : highNormUpperX UpperResult16 19 = UpperField16Rows 19 := by decide +kernel
theorem UpperField16_rows (x : Fin 20) : highNormUpperX UpperResult16 x = UpperField16Rows x := by
  fin_cases x
  · exact UpperField16X0
  · exact UpperField16X1
  · exact UpperField16X2
  · exact UpperField16X3
  · exact UpperField16X4
  · exact UpperField16X5
  · exact UpperField16X6
  · exact UpperField16X7
  · exact UpperField16X8
  · exact UpperField16X9
  · exact UpperField16X10
  · exact UpperField16X11
  · exact UpperField16X12
  · exact UpperField16X13
  · exact UpperField16X14
  · exact UpperField16X15
  · exact UpperField16X16
  · exact UpperField16X17
  · exact UpperField16X18
  · exact UpperField16X19
theorem UpperField16_bound : highNormUpper UpperResult16 ≤ 94474788609195743926284640732132 :=
  highNormUpper_le_of_rows UpperResult16 UpperField16Rows 94474788609195743926284640732132 UpperField16_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
