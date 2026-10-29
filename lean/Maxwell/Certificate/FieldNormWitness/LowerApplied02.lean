import Maxwell.Certificate.AppliedWitness.LowerApplied2
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied02Rows : Fin 20 → ℤ := ![43387967846908, 242550130248358, 275425347657786, 322298910476235, 380942950227943, 87387421214069, 459903854407342, 463119922356617, 456489535342065, 441848076932807, 91347015804323, 474505800260817, 467788266797128, 451883757457652, 427721377590336, 77817434533532, 327736891414775, 271847893355832, 231753740625011, 209216835625495]
theorem LowerApplied02X0 : highNormUpperX LowerApplied2 0 = LowerApplied02Rows 0 := by decide +kernel
theorem LowerApplied02X1 : highNormUpperX LowerApplied2 1 = LowerApplied02Rows 1 := by decide +kernel
theorem LowerApplied02X2 : highNormUpperX LowerApplied2 2 = LowerApplied02Rows 2 := by decide +kernel
theorem LowerApplied02X3 : highNormUpperX LowerApplied2 3 = LowerApplied02Rows 3 := by decide +kernel
theorem LowerApplied02X4 : highNormUpperX LowerApplied2 4 = LowerApplied02Rows 4 := by decide +kernel
theorem LowerApplied02X5 : highNormUpperX LowerApplied2 5 = LowerApplied02Rows 5 := by decide +kernel
theorem LowerApplied02X6 : highNormUpperX LowerApplied2 6 = LowerApplied02Rows 6 := by decide +kernel
theorem LowerApplied02X7 : highNormUpperX LowerApplied2 7 = LowerApplied02Rows 7 := by decide +kernel
theorem LowerApplied02X8 : highNormUpperX LowerApplied2 8 = LowerApplied02Rows 8 := by decide +kernel
theorem LowerApplied02X9 : highNormUpperX LowerApplied2 9 = LowerApplied02Rows 9 := by decide +kernel
theorem LowerApplied02X10 : highNormUpperX LowerApplied2 10 = LowerApplied02Rows 10 := by decide +kernel
theorem LowerApplied02X11 : highNormUpperX LowerApplied2 11 = LowerApplied02Rows 11 := by decide +kernel
theorem LowerApplied02X12 : highNormUpperX LowerApplied2 12 = LowerApplied02Rows 12 := by decide +kernel
theorem LowerApplied02X13 : highNormUpperX LowerApplied2 13 = LowerApplied02Rows 13 := by decide +kernel
theorem LowerApplied02X14 : highNormUpperX LowerApplied2 14 = LowerApplied02Rows 14 := by decide +kernel
theorem LowerApplied02X15 : highNormUpperX LowerApplied2 15 = LowerApplied02Rows 15 := by decide +kernel
theorem LowerApplied02X16 : highNormUpperX LowerApplied2 16 = LowerApplied02Rows 16 := by decide +kernel
theorem LowerApplied02X17 : highNormUpperX LowerApplied2 17 = LowerApplied02Rows 17 := by decide +kernel
theorem LowerApplied02X18 : highNormUpperX LowerApplied2 18 = LowerApplied02Rows 18 := by decide +kernel
theorem LowerApplied02X19 : highNormUpperX LowerApplied2 19 = LowerApplied02Rows 19 := by decide +kernel
theorem LowerApplied02_rows (x : Fin 20) : highNormUpperX LowerApplied2 x = LowerApplied02Rows x := by
  fin_cases x
  · exact LowerApplied02X0
  · exact LowerApplied02X1
  · exact LowerApplied02X2
  · exact LowerApplied02X3
  · exact LowerApplied02X4
  · exact LowerApplied02X5
  · exact LowerApplied02X6
  · exact LowerApplied02X7
  · exact LowerApplied02X8
  · exact LowerApplied02X9
  · exact LowerApplied02X10
  · exact LowerApplied02X11
  · exact LowerApplied02X12
  · exact LowerApplied02X13
  · exact LowerApplied02X14
  · exact LowerApplied02X15
  · exact LowerApplied02X16
  · exact LowerApplied02X17
  · exact LowerApplied02X18
  · exact LowerApplied02X19
theorem LowerApplied02_bound : highNormUpper LowerApplied2 ≤ 6204973130175031 :=
  highNormUpper_le_of_rows LowerApplied2 LowerApplied02Rows 6204973130175031 LowerApplied02_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
