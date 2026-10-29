import Maxwell.Certificate.ProjectionWitness.LowerResult23
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField23Rows : Fin 20 → ℤ := ![20679171793736332322448248904711, 13500579544519204500630860741400, 20080301505436079458123246837008, 1333950364447784967680984857362, 329506258007686068290773217904, 163824179035647544252154846799, 44203046263080220413979345166, 29785148971513865089629399611, 9776264425177876602351587647, 6629054990687786689055392253, 6629054990687767921791836823, 9776264425178326589222366640, 29785148971513237609133873196, 44203046263079826466705769618, 163824179035643065897676353870, 329506258007688646634942732777, 1333950364447770035782096404562, 20080301505436058826934304544191, 13500579544519362570940941058353, 20679171793736667017686158484641]
theorem LowerField23X0 : highNormUpperX LowerResult23 0 = LowerField23Rows 0 := by decide +kernel
theorem LowerField23X1 : highNormUpperX LowerResult23 1 = LowerField23Rows 1 := by decide +kernel
theorem LowerField23X2 : highNormUpperX LowerResult23 2 = LowerField23Rows 2 := by decide +kernel
theorem LowerField23X3 : highNormUpperX LowerResult23 3 = LowerField23Rows 3 := by decide +kernel
theorem LowerField23X4 : highNormUpperX LowerResult23 4 = LowerField23Rows 4 := by decide +kernel
theorem LowerField23X5 : highNormUpperX LowerResult23 5 = LowerField23Rows 5 := by decide +kernel
theorem LowerField23X6 : highNormUpperX LowerResult23 6 = LowerField23Rows 6 := by decide +kernel
theorem LowerField23X7 : highNormUpperX LowerResult23 7 = LowerField23Rows 7 := by decide +kernel
theorem LowerField23X8 : highNormUpperX LowerResult23 8 = LowerField23Rows 8 := by decide +kernel
theorem LowerField23X9 : highNormUpperX LowerResult23 9 = LowerField23Rows 9 := by decide +kernel
theorem LowerField23X10 : highNormUpperX LowerResult23 10 = LowerField23Rows 10 := by decide +kernel
theorem LowerField23X11 : highNormUpperX LowerResult23 11 = LowerField23Rows 11 := by decide +kernel
theorem LowerField23X12 : highNormUpperX LowerResult23 12 = LowerField23Rows 12 := by decide +kernel
theorem LowerField23X13 : highNormUpperX LowerResult23 13 = LowerField23Rows 13 := by decide +kernel
theorem LowerField23X14 : highNormUpperX LowerResult23 14 = LowerField23Rows 14 := by decide +kernel
theorem LowerField23X15 : highNormUpperX LowerResult23 15 = LowerField23Rows 15 := by decide +kernel
theorem LowerField23X16 : highNormUpperX LowerResult23 16 = LowerField23Rows 16 := by decide +kernel
theorem LowerField23X17 : highNormUpperX LowerResult23 17 = LowerField23Rows 17 := by decide +kernel
theorem LowerField23X18 : highNormUpperX LowerResult23 18 = LowerField23Rows 18 := by decide +kernel
theorem LowerField23X19 : highNormUpperX LowerResult23 19 = LowerField23Rows 19 := by decide +kernel
theorem LowerField23_rows (x : Fin 20) : highNormUpperX LowerResult23 x = LowerField23Rows x := by
  fin_cases x
  · exact LowerField23X0
  · exact LowerField23X1
  · exact LowerField23X2
  · exact LowerField23X3
  · exact LowerField23X4
  · exact LowerField23X5
  · exact LowerField23X6
  · exact LowerField23X7
  · exact LowerField23X8
  · exact LowerField23X9
  · exact LowerField23X10
  · exact LowerField23X11
  · exact LowerField23X12
  · exact LowerField23X13
  · exact LowerField23X14
  · exact LowerField23X15
  · exact LowerField23X16
  · exact LowerField23X17
  · exact LowerField23X18
  · exact LowerField23X19
theorem LowerField23_bound : highNormUpper LowerResult23 ≤ 112355454319666843932684258554532 :=
  highNormUpper_le_of_rows LowerResult23 LowerField23Rows 112355454319666843932684258554532 LowerField23_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
