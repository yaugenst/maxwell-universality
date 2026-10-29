import Maxwell.Certificate.ProjectionWitness.UpperResult24
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField24Rows : Fin 20 → ℤ := ![28599789539021399209524567890423, 3886528379659850442427457239650, 18084736051912532501669372292972, 1486278950207187353705047635265, 243861846620168945069804566774, 178484425121966184768267324083, 33455694910177931524765970086, 31871247257547049133936747415, 6734082767909795654194359515, 5385867442300209741018707692, 5385867442300231032469653320, 6734082767909469100072250117, 31871247257548249778186189831, 33455694910178275172590245688, 178484425121970458079495003665, 243861846620178233584884049403, 1486278950207222877159656841446, 18084736051913161721296701375846, 3886528379659979981110628087877, 28599789539020973519453113470238]
theorem UpperField24X0 : highNormUpperX UpperResult24 0 = UpperField24Rows 0 := by decide +kernel
theorem UpperField24X1 : highNormUpperX UpperResult24 1 = UpperField24Rows 1 := by decide +kernel
theorem UpperField24X2 : highNormUpperX UpperResult24 2 = UpperField24Rows 2 := by decide +kernel
theorem UpperField24X3 : highNormUpperX UpperResult24 3 = UpperField24Rows 3 := by decide +kernel
theorem UpperField24X4 : highNormUpperX UpperResult24 4 = UpperField24Rows 4 := by decide +kernel
theorem UpperField24X5 : highNormUpperX UpperResult24 5 = UpperField24Rows 5 := by decide +kernel
theorem UpperField24X6 : highNormUpperX UpperResult24 6 = UpperField24Rows 6 := by decide +kernel
theorem UpperField24X7 : highNormUpperX UpperResult24 7 = UpperField24Rows 7 := by decide +kernel
theorem UpperField24X8 : highNormUpperX UpperResult24 8 = UpperField24Rows 8 := by decide +kernel
theorem UpperField24X9 : highNormUpperX UpperResult24 9 = UpperField24Rows 9 := by decide +kernel
theorem UpperField24X10 : highNormUpperX UpperResult24 10 = UpperField24Rows 10 := by decide +kernel
theorem UpperField24X11 : highNormUpperX UpperResult24 11 = UpperField24Rows 11 := by decide +kernel
theorem UpperField24X12 : highNormUpperX UpperResult24 12 = UpperField24Rows 12 := by decide +kernel
theorem UpperField24X13 : highNormUpperX UpperResult24 13 = UpperField24Rows 13 := by decide +kernel
theorem UpperField24X14 : highNormUpperX UpperResult24 14 = UpperField24Rows 14 := by decide +kernel
theorem UpperField24X15 : highNormUpperX UpperResult24 15 = UpperField24Rows 15 := by decide +kernel
theorem UpperField24X16 : highNormUpperX UpperResult24 16 = UpperField24Rows 16 := by decide +kernel
theorem UpperField24X17 : highNormUpperX UpperResult24 17 = UpperField24Rows 17 := by decide +kernel
theorem UpperField24X18 : highNormUpperX UpperResult24 18 = UpperField24Rows 18 := by decide +kernel
theorem UpperField24X19 : highNormUpperX UpperResult24 19 = UpperField24Rows 19 := by decide +kernel
theorem UpperField24_rows (x : Fin 20) : highNormUpperX UpperResult24 x = UpperField24Rows x := by
  fin_cases x
  · exact UpperField24X0
  · exact UpperField24X1
  · exact UpperField24X2
  · exact UpperField24X3
  · exact UpperField24X4
  · exact UpperField24X5
  · exact UpperField24X6
  · exact UpperField24X7
  · exact UpperField24X8
  · exact UpperField24X9
  · exact UpperField24X10
  · exact UpperField24X11
  · exact UpperField24X12
  · exact UpperField24X13
  · exact UpperField24X14
  · exact UpperField24X15
  · exact UpperField24X16
  · exact UpperField24X17
  · exact UpperField24X18
  · exact UpperField24X19
theorem UpperField24_bound : highNormUpper UpperResult24 ≤ 105114252169842462638986229901306 :=
  highNormUpper_le_of_rows UpperResult24 UpperField24Rows 105114252169842462638986229901306 UpperField24_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
