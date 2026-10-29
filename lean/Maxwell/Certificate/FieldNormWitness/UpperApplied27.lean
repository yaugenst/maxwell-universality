import Maxwell.Certificate.AppliedWitness.UpperApplied27
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperApplied27Rows : Fin 20 → ℤ := ![15002899680900, 83233044387711, 95012544321932, 111236938958344, 130866705434711, 30259170227757, 158121240191641, 160066836710461, 157755145326201, 151860017926074, 31626176308103, 163137966307709, 161678179392190, 156164900362836, 147011644363897, 26931224066663, 112529426356135, 93776328922609, 79934177440228, 71809938382657]
theorem UpperApplied27X0 : highNormUpperX UpperApplied27 0 = UpperApplied27Rows 0 := by decide +kernel
theorem UpperApplied27X1 : highNormUpperX UpperApplied27 1 = UpperApplied27Rows 1 := by decide +kernel
theorem UpperApplied27X2 : highNormUpperX UpperApplied27 2 = UpperApplied27Rows 2 := by decide +kernel
theorem UpperApplied27X3 : highNormUpperX UpperApplied27 3 = UpperApplied27Rows 3 := by decide +kernel
theorem UpperApplied27X4 : highNormUpperX UpperApplied27 4 = UpperApplied27Rows 4 := by decide +kernel
theorem UpperApplied27X5 : highNormUpperX UpperApplied27 5 = UpperApplied27Rows 5 := by decide +kernel
theorem UpperApplied27X6 : highNormUpperX UpperApplied27 6 = UpperApplied27Rows 6 := by decide +kernel
theorem UpperApplied27X7 : highNormUpperX UpperApplied27 7 = UpperApplied27Rows 7 := by decide +kernel
theorem UpperApplied27X8 : highNormUpperX UpperApplied27 8 = UpperApplied27Rows 8 := by decide +kernel
theorem UpperApplied27X9 : highNormUpperX UpperApplied27 9 = UpperApplied27Rows 9 := by decide +kernel
theorem UpperApplied27X10 : highNormUpperX UpperApplied27 10 = UpperApplied27Rows 10 := by decide +kernel
theorem UpperApplied27X11 : highNormUpperX UpperApplied27 11 = UpperApplied27Rows 11 := by decide +kernel
theorem UpperApplied27X12 : highNormUpperX UpperApplied27 12 = UpperApplied27Rows 12 := by decide +kernel
theorem UpperApplied27X13 : highNormUpperX UpperApplied27 13 = UpperApplied27Rows 13 := by decide +kernel
theorem UpperApplied27X14 : highNormUpperX UpperApplied27 14 = UpperApplied27Rows 14 := by decide +kernel
theorem UpperApplied27X15 : highNormUpperX UpperApplied27 15 = UpperApplied27Rows 15 := by decide +kernel
theorem UpperApplied27X16 : highNormUpperX UpperApplied27 16 = UpperApplied27Rows 16 := by decide +kernel
theorem UpperApplied27X17 : highNormUpperX UpperApplied27 17 = UpperApplied27Rows 17 := by decide +kernel
theorem UpperApplied27X18 : highNormUpperX UpperApplied27 18 = UpperApplied27Rows 18 := by decide +kernel
theorem UpperApplied27X19 : highNormUpperX UpperApplied27 19 = UpperApplied27Rows 19 := by decide +kernel
theorem UpperApplied27_rows (x : Fin 20) : highNormUpperX UpperApplied27 x = UpperApplied27Rows x := by
  fin_cases x
  · exact UpperApplied27X0
  · exact UpperApplied27X1
  · exact UpperApplied27X2
  · exact UpperApplied27X3
  · exact UpperApplied27X4
  · exact UpperApplied27X5
  · exact UpperApplied27X6
  · exact UpperApplied27X7
  · exact UpperApplied27X8
  · exact UpperApplied27X9
  · exact UpperApplied27X10
  · exact UpperApplied27X11
  · exact UpperApplied27X12
  · exact UpperApplied27X13
  · exact UpperApplied27X14
  · exact UpperApplied27X15
  · exact UpperApplied27X16
  · exact UpperApplied27X17
  · exact UpperApplied27X18
  · exact UpperApplied27X19
theorem UpperApplied27_bound : highNormUpper UpperApplied27 ≤ 2138014505068759 :=
  highNormUpper_le_of_rows UpperApplied27 UpperApplied27Rows 2138014505068759 UpperApplied27_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
