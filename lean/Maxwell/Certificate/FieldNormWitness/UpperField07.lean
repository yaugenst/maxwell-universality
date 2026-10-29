import Maxwell.Certificate.ProjectionWitness.UpperResult7
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField07Rows : Fin 20 → ℤ := ![15287811576942164488664926786448, 7746735760984378761924264435471, 11883309228938088918636797238452, 547858305990892173875945948333, 237492814396288145984567513884, 71355601119680426712709115005, 36075726055177067045916617954, 18672930285288406627099913453, 9207643435081111744698472955, 6117576092730188726096700208, 6117576092730553715731497111, 9207643435081307419480086687, 18672930285289685976023032220, 36075726055179717813575965591, 71355601119685372511356887279, 237492814396310556575106503285, 547858305990924937517608222805, 11883309228939796527629172733244, 7746735760985096318208651856104, 15287811576941216353221928412851]
theorem UpperField07X0 : highNormUpperX UpperResult7 0 = UpperField07Rows 0 := by decide +kernel
theorem UpperField07X1 : highNormUpperX UpperResult7 1 = UpperField07Rows 1 := by decide +kernel
theorem UpperField07X2 : highNormUpperX UpperResult7 2 = UpperField07Rows 2 := by decide +kernel
theorem UpperField07X3 : highNormUpperX UpperResult7 3 = UpperField07Rows 3 := by decide +kernel
theorem UpperField07X4 : highNormUpperX UpperResult7 4 = UpperField07Rows 4 := by decide +kernel
theorem UpperField07X5 : highNormUpperX UpperResult7 5 = UpperField07Rows 5 := by decide +kernel
theorem UpperField07X6 : highNormUpperX UpperResult7 6 = UpperField07Rows 6 := by decide +kernel
theorem UpperField07X7 : highNormUpperX UpperResult7 7 = UpperField07Rows 7 := by decide +kernel
theorem UpperField07X8 : highNormUpperX UpperResult7 8 = UpperField07Rows 8 := by decide +kernel
theorem UpperField07X9 : highNormUpperX UpperResult7 9 = UpperField07Rows 9 := by decide +kernel
theorem UpperField07X10 : highNormUpperX UpperResult7 10 = UpperField07Rows 10 := by decide +kernel
theorem UpperField07X11 : highNormUpperX UpperResult7 11 = UpperField07Rows 11 := by decide +kernel
theorem UpperField07X12 : highNormUpperX UpperResult7 12 = UpperField07Rows 12 := by decide +kernel
theorem UpperField07X13 : highNormUpperX UpperResult7 13 = UpperField07Rows 13 := by decide +kernel
theorem UpperField07X14 : highNormUpperX UpperResult7 14 = UpperField07Rows 14 := by decide +kernel
theorem UpperField07X15 : highNormUpperX UpperResult7 15 = UpperField07Rows 15 := by decide +kernel
theorem UpperField07X16 : highNormUpperX UpperResult7 16 = UpperField07Rows 16 := by decide +kernel
theorem UpperField07X17 : highNormUpperX UpperResult7 17 = UpperField07Rows 17 := by decide +kernel
theorem UpperField07X18 : highNormUpperX UpperResult7 18 = UpperField07Rows 18 := by decide +kernel
theorem UpperField07X19 : highNormUpperX UpperResult7 19 = UpperField07Rows 19 := by decide +kernel
theorem UpperField07_rows (x : Fin 20) : highNormUpperX UpperResult7 x = UpperField07Rows x := by
  fin_cases x
  · exact UpperField07X0
  · exact UpperField07X1
  · exact UpperField07X2
  · exact UpperField07X3
  · exact UpperField07X4
  · exact UpperField07X5
  · exact UpperField07X6
  · exact UpperField07X7
  · exact UpperField07X8
  · exact UpperField07X9
  · exact UpperField07X10
  · exact UpperField07X11
  · exact UpperField07X12
  · exact UpperField07X13
  · exact UpperField07X14
  · exact UpperField07X15
  · exact UpperField07X16
  · exact UpperField07X17
  · exact UpperField07X18
  · exact UpperField07X19
theorem UpperField07_bound : highNormUpper UpperResult7 ≤ 71689274328481081020531657939340 :=
  highNormUpper_le_of_rows UpperResult7 UpperField07Rows 71689274328481081020531657939340 UpperField07_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
