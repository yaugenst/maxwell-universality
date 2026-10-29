import Maxwell.Certificate.ProjectionWitness.LowerResult2
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField02Rows : Fin 20 → ℤ := ![30531241660138418593032137333806, 179686580149853282734298852576859, 52599847650513747420992763765659, 5457435023704668436435192487534, 4239828484693866438520210414621, 526184495811934565406243772565, 716601276853408228667475261469, 141873392101298684570088805313, 166095285004050273461951459151, 45214290995643906698523892765, 45214290995643519363373561286, 166095285004048936341387195092, 141873392101296469803146479648, 716601276853405155456448000067, 526184495811924327381015566811, 4239828484693823990939709673117, 5457435023704560186059921371640, 52599847650514024768586780850945, 179686580149856030768695222728375, 30531241660138422877923806592834]
theorem LowerField02X0 : highNormUpperX LowerResult2 0 = LowerField02Rows 0 := by decide +kernel
theorem LowerField02X1 : highNormUpperX LowerResult2 1 = LowerField02Rows 1 := by decide +kernel
theorem LowerField02X2 : highNormUpperX LowerResult2 2 = LowerField02Rows 2 := by decide +kernel
theorem LowerField02X3 : highNormUpperX LowerResult2 3 = LowerField02Rows 3 := by decide +kernel
theorem LowerField02X4 : highNormUpperX LowerResult2 4 = LowerField02Rows 4 := by decide +kernel
theorem LowerField02X5 : highNormUpperX LowerResult2 5 = LowerField02Rows 5 := by decide +kernel
theorem LowerField02X6 : highNormUpperX LowerResult2 6 = LowerField02Rows 6 := by decide +kernel
theorem LowerField02X7 : highNormUpperX LowerResult2 7 = LowerField02Rows 7 := by decide +kernel
theorem LowerField02X8 : highNormUpperX LowerResult2 8 = LowerField02Rows 8 := by decide +kernel
theorem LowerField02X9 : highNormUpperX LowerResult2 9 = LowerField02Rows 9 := by decide +kernel
theorem LowerField02X10 : highNormUpperX LowerResult2 10 = LowerField02Rows 10 := by decide +kernel
theorem LowerField02X11 : highNormUpperX LowerResult2 11 = LowerField02Rows 11 := by decide +kernel
theorem LowerField02X12 : highNormUpperX LowerResult2 12 = LowerField02Rows 12 := by decide +kernel
theorem LowerField02X13 : highNormUpperX LowerResult2 13 = LowerField02Rows 13 := by decide +kernel
theorem LowerField02X14 : highNormUpperX LowerResult2 14 = LowerField02Rows 14 := by decide +kernel
theorem LowerField02X15 : highNormUpperX LowerResult2 15 = LowerField02Rows 15 := by decide +kernel
theorem LowerField02X16 : highNormUpperX LowerResult2 16 = LowerField02Rows 16 := by decide +kernel
theorem LowerField02X17 : highNormUpperX LowerResult2 17 = LowerField02Rows 17 := by decide +kernel
theorem LowerField02X18 : highNormUpperX LowerResult2 18 = LowerField02Rows 18 := by decide +kernel
theorem LowerField02X19 : highNormUpperX LowerResult2 19 = LowerField02Rows 19 := by decide +kernel
theorem LowerField02_rows (x : Fin 20) : highNormUpperX LowerResult2 x = LowerField02Rows x := by
  fin_cases x
  · exact LowerField02X0
  · exact LowerField02X1
  · exact LowerField02X2
  · exact LowerField02X3
  · exact LowerField02X4
  · exact LowerField02X5
  · exact LowerField02X6
  · exact LowerField02X7
  · exact LowerField02X8
  · exact LowerField02X9
  · exact LowerField02X10
  · exact LowerField02X11
  · exact LowerField02X12
  · exact LowerField02X13
  · exact LowerField02X14
  · exact LowerField02X15
  · exact LowerField02X16
  · exact LowerField02X17
  · exact LowerField02X18
  · exact LowerField02X19
theorem LowerField02_bound : highNormUpper LowerResult2 ≤ 548221803419343500282634251789557 :=
  highNormUpper_le_of_rows LowerResult2 LowerField02Rows 548221803419343500282634251789557 LowerField02_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
