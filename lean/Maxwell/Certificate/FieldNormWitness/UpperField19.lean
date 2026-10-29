import Maxwell.Certificate.ProjectionWitness.UpperResult19
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField19Rows : Fin 20 → ℤ := ![16852302619392463238233251341004, 6795874587205566476147284721688, 15456110563517203430665059747444, 634205919371211436528120917308, 201560514236409398443960530860, 94537704892583011422203430122, 21671440990624708566521113442, 25108923978434420700961857283, 5518450440239081112825137027, 7703414415855998986330424511, 7703414415856210598657432348, 5518450440239336546442550166, 25108923978434361399933026006, 21671440990625202023478087703, 94537704892582477458749873011, 201560514236410575744736372382, 634205919371211993760602380131, 15456110563517170245617941587666, 6795874587205796230583951352644, 16852302619392459695654899225289]
theorem UpperField19X0 : highNormUpperX UpperResult19 0 = UpperField19Rows 0 := by decide +kernel
theorem UpperField19X1 : highNormUpperX UpperResult19 1 = UpperField19Rows 1 := by decide +kernel
theorem UpperField19X2 : highNormUpperX UpperResult19 2 = UpperField19Rows 2 := by decide +kernel
theorem UpperField19X3 : highNormUpperX UpperResult19 3 = UpperField19Rows 3 := by decide +kernel
theorem UpperField19X4 : highNormUpperX UpperResult19 4 = UpperField19Rows 4 := by decide +kernel
theorem UpperField19X5 : highNormUpperX UpperResult19 5 = UpperField19Rows 5 := by decide +kernel
theorem UpperField19X6 : highNormUpperX UpperResult19 6 = UpperField19Rows 6 := by decide +kernel
theorem UpperField19X7 : highNormUpperX UpperResult19 7 = UpperField19Rows 7 := by decide +kernel
theorem UpperField19X8 : highNormUpperX UpperResult19 8 = UpperField19Rows 8 := by decide +kernel
theorem UpperField19X9 : highNormUpperX UpperResult19 9 = UpperField19Rows 9 := by decide +kernel
theorem UpperField19X10 : highNormUpperX UpperResult19 10 = UpperField19Rows 10 := by decide +kernel
theorem UpperField19X11 : highNormUpperX UpperResult19 11 = UpperField19Rows 11 := by decide +kernel
theorem UpperField19X12 : highNormUpperX UpperResult19 12 = UpperField19Rows 12 := by decide +kernel
theorem UpperField19X13 : highNormUpperX UpperResult19 13 = UpperField19Rows 13 := by decide +kernel
theorem UpperField19X14 : highNormUpperX UpperResult19 14 = UpperField19Rows 14 := by decide +kernel
theorem UpperField19X15 : highNormUpperX UpperResult19 15 = UpperField19Rows 15 := by decide +kernel
theorem UpperField19X16 : highNormUpperX UpperResult19 16 = UpperField19Rows 16 := by decide +kernel
theorem UpperField19X17 : highNormUpperX UpperResult19 17 = UpperField19Rows 17 := by decide +kernel
theorem UpperField19X18 : highNormUpperX UpperResult19 18 = UpperField19Rows 18 := by decide +kernel
theorem UpperField19X19 : highNormUpperX UpperResult19 19 = UpperField19Rows 19 := by decide +kernel
theorem UpperField19_rows (x : Fin 20) : highNormUpperX UpperResult19 x = UpperField19Rows x := by
  fin_cases x
  · exact UpperField19X0
  · exact UpperField19X1
  · exact UpperField19X2
  · exact UpperField19X3
  · exact UpperField19X4
  · exact UpperField19X5
  · exact UpperField19X6
  · exact UpperField19X7
  · exact UpperField19X8
  · exact UpperField19X9
  · exact UpperField19X10
  · exact UpperField19X11
  · exact UpperField19X12
  · exact UpperField19X13
  · exact UpperField19X14
  · exact UpperField19X15
  · exact UpperField19X16
  · exact UpperField19X17
  · exact UpperField19X18
  · exact UpperField19X19
theorem UpperField19_bound : highNormUpper UpperResult19 ≤ 80189188276881377530195911108035 :=
  highNormUpper_le_of_rows UpperResult19 UpperField19Rows 80189188276881377530195911108035 UpperField19_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
