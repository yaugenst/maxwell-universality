import Maxwell.Certificate.ProjectionWitness.LowerResult19
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerField19Rows : Fin 20 → ℤ := ![15438710391988282348146696145770, 8529757004625768317135314936316, 16185283751447119244546255210000, 873265773340391042352971353163, 215666512610477510387866024317, 118796510467378675544889699838, 26591041719724246737232356093, 31432784402793811988600069581, 7351747595849376079836682094, 9810465972509234741008021427, 9810465972509602191259783102, 7351747595849576504440528147, 31432784402794314781841639398, 26591041719725075559018257501, 118796510467379989667211165471, 215666512610482640257587508594, 873265773340394989220715051862, 16185283751447437183500628060608, 8529757004625789359972316886094, 15438710391988337537372027471922]
theorem LowerField19X0 : highNormUpperX LowerResult19 0 = LowerField19Rows 0 := by decide +kernel
theorem LowerField19X1 : highNormUpperX LowerResult19 1 = LowerField19Rows 1 := by decide +kernel
theorem LowerField19X2 : highNormUpperX LowerResult19 2 = LowerField19Rows 2 := by decide +kernel
theorem LowerField19X3 : highNormUpperX LowerResult19 3 = LowerField19Rows 3 := by decide +kernel
theorem LowerField19X4 : highNormUpperX LowerResult19 4 = LowerField19Rows 4 := by decide +kernel
theorem LowerField19X5 : highNormUpperX LowerResult19 5 = LowerField19Rows 5 := by decide +kernel
theorem LowerField19X6 : highNormUpperX LowerResult19 6 = LowerField19Rows 6 := by decide +kernel
theorem LowerField19X7 : highNormUpperX LowerResult19 7 = LowerField19Rows 7 := by decide +kernel
theorem LowerField19X8 : highNormUpperX LowerResult19 8 = LowerField19Rows 8 := by decide +kernel
theorem LowerField19X9 : highNormUpperX LowerResult19 9 = LowerField19Rows 9 := by decide +kernel
theorem LowerField19X10 : highNormUpperX LowerResult19 10 = LowerField19Rows 10 := by decide +kernel
theorem LowerField19X11 : highNormUpperX LowerResult19 11 = LowerField19Rows 11 := by decide +kernel
theorem LowerField19X12 : highNormUpperX LowerResult19 12 = LowerField19Rows 12 := by decide +kernel
theorem LowerField19X13 : highNormUpperX LowerResult19 13 = LowerField19Rows 13 := by decide +kernel
theorem LowerField19X14 : highNormUpperX LowerResult19 14 = LowerField19Rows 14 := by decide +kernel
theorem LowerField19X15 : highNormUpperX LowerResult19 15 = LowerField19Rows 15 := by decide +kernel
theorem LowerField19X16 : highNormUpperX LowerResult19 16 = LowerField19Rows 16 := by decide +kernel
theorem LowerField19X17 : highNormUpperX LowerResult19 17 = LowerField19Rows 17 := by decide +kernel
theorem LowerField19X18 : highNormUpperX LowerResult19 18 = LowerField19Rows 18 := by decide +kernel
theorem LowerField19X19 : highNormUpperX LowerResult19 19 = LowerField19Rows 19 := by decide +kernel
theorem LowerField19_rows (x : Fin 20) : highNormUpperX LowerResult19 x = LowerField19Rows x := by
  fin_cases x
  · exact LowerField19X0
  · exact LowerField19X1
  · exact LowerField19X2
  · exact LowerField19X3
  · exact LowerField19X4
  · exact LowerField19X5
  · exact LowerField19X6
  · exact LowerField19X7
  · exact LowerField19X8
  · exact LowerField19X9
  · exact LowerField19X10
  · exact LowerField19X11
  · exact LowerField19X12
  · exact LowerField19X13
  · exact LowerField19X14
  · exact LowerField19X15
  · exact LowerField19X16
  · exact LowerField19X17
  · exact LowerField19X18
  · exact LowerField19X19
theorem LowerField19_bound : highNormUpper LowerResult19 ≤ 82873331968340994076687716851298 :=
  highNormUpper_le_of_rows LowerResult19 LowerField19Rows 82873331968340994076687716851298 LowerField19_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
