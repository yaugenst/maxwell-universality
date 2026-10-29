import Maxwell.Certificate.ProjectionWitness.UpperResult27
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField27Rows : Fin 20 → ℤ := ![5944329218555684069978993852287, 10013787524258557431465297044258, 12420753200258311790301619704761, 1049648769526791925958539236649, 282559342677579223687591766658, 120620861294408720364992919197, 42596961338437130666356485691, 21317965574778580251666993129, 4395220217431440492372791552, 5032473907181202279589685813, 5032473907180841359589109168, 4395220217431496788352867761, 21317965574778647869099039277, 42596961338437052662378504642, 120620861294410403369165078024, 282559342677581095959772375871, 1049648769526798234591557942733, 12420753200258374093232728985865, 10013787524258547328214071681058, 5944329218555707722538647300560]
theorem UpperField27X0 : highNormUpperX UpperResult27 0 = UpperField27Rows 0 := by decide +kernel
theorem UpperField27X1 : highNormUpperX UpperResult27 1 = UpperField27Rows 1 := by decide +kernel
theorem UpperField27X2 : highNormUpperX UpperResult27 2 = UpperField27Rows 2 := by decide +kernel
theorem UpperField27X3 : highNormUpperX UpperResult27 3 = UpperField27Rows 3 := by decide +kernel
theorem UpperField27X4 : highNormUpperX UpperResult27 4 = UpperField27Rows 4 := by decide +kernel
theorem UpperField27X5 : highNormUpperX UpperResult27 5 = UpperField27Rows 5 := by decide +kernel
theorem UpperField27X6 : highNormUpperX UpperResult27 6 = UpperField27Rows 6 := by decide +kernel
theorem UpperField27X7 : highNormUpperX UpperResult27 7 = UpperField27Rows 7 := by decide +kernel
theorem UpperField27X8 : highNormUpperX UpperResult27 8 = UpperField27Rows 8 := by decide +kernel
theorem UpperField27X9 : highNormUpperX UpperResult27 9 = UpperField27Rows 9 := by decide +kernel
theorem UpperField27X10 : highNormUpperX UpperResult27 10 = UpperField27Rows 10 := by decide +kernel
theorem UpperField27X11 : highNormUpperX UpperResult27 11 = UpperField27Rows 11 := by decide +kernel
theorem UpperField27X12 : highNormUpperX UpperResult27 12 = UpperField27Rows 12 := by decide +kernel
theorem UpperField27X13 : highNormUpperX UpperResult27 13 = UpperField27Rows 13 := by decide +kernel
theorem UpperField27X14 : highNormUpperX UpperResult27 14 = UpperField27Rows 14 := by decide +kernel
theorem UpperField27X15 : highNormUpperX UpperResult27 15 = UpperField27Rows 15 := by decide +kernel
theorem UpperField27X16 : highNormUpperX UpperResult27 16 = UpperField27Rows 16 := by decide +kernel
theorem UpperField27X17 : highNormUpperX UpperResult27 17 = UpperField27Rows 17 := by decide +kernel
theorem UpperField27X18 : highNormUpperX UpperResult27 18 = UpperField27Rows 18 := by decide +kernel
theorem UpperField27X19 : highNormUpperX UpperResult27 19 = UpperField27Rows 19 := by decide +kernel
theorem UpperField27_rows (x : Fin 20) : highNormUpperX UpperResult27 x = UpperField27Rows x := by
  fin_cases x
  · exact UpperField27X0
  · exact UpperField27X1
  · exact UpperField27X2
  · exact UpperField27X3
  · exact UpperField27X4
  · exact UpperField27X5
  · exact UpperField27X6
  · exact UpperField27X7
  · exact UpperField27X8
  · exact UpperField27X9
  · exact UpperField27X10
  · exact UpperField27X11
  · exact UpperField27X12
  · exact UpperField27X13
  · exact UpperField27X14
  · exact UpperField27X15
  · exact UpperField27X16
  · exact UpperField27X17
  · exact UpperField27X18
  · exact UpperField27X19
theorem UpperField27_bound : highNormUpper UpperResult27 ≤ 59810083075218408432032383364954 :=
  highNormUpper_le_of_rows UpperResult27 UpperField27Rows 59810083075218408432032383364954 UpperField27_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
