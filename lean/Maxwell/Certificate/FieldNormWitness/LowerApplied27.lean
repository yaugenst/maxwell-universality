import Maxwell.Certificate.AppliedWitness.LowerApplied27
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied27Rows : Fin 20 → ℤ := ![39013689310307, 218072182683581, 247672277353234, 289918718977396, 342750313138395, 78655454009170, 414012551601895, 416982983254592, 410974002143613, 397659584334666, 82210387259411, 427147833318317, 421181902075195, 406829790767808, 384971199241328, 70015257219700, 294782947379360, 244453600932530, 208378622883687, 188125580471829]
theorem LowerApplied27X0 : highNormUpperX LowerApplied27 0 = LowerApplied27Rows 0 := by decide +kernel
theorem LowerApplied27X1 : highNormUpperX LowerApplied27 1 = LowerApplied27Rows 1 := by decide +kernel
theorem LowerApplied27X2 : highNormUpperX LowerApplied27 2 = LowerApplied27Rows 2 := by decide +kernel
theorem LowerApplied27X3 : highNormUpperX LowerApplied27 3 = LowerApplied27Rows 3 := by decide +kernel
theorem LowerApplied27X4 : highNormUpperX LowerApplied27 4 = LowerApplied27Rows 4 := by decide +kernel
theorem LowerApplied27X5 : highNormUpperX LowerApplied27 5 = LowerApplied27Rows 5 := by decide +kernel
theorem LowerApplied27X6 : highNormUpperX LowerApplied27 6 = LowerApplied27Rows 6 := by decide +kernel
theorem LowerApplied27X7 : highNormUpperX LowerApplied27 7 = LowerApplied27Rows 7 := by decide +kernel
theorem LowerApplied27X8 : highNormUpperX LowerApplied27 8 = LowerApplied27Rows 8 := by decide +kernel
theorem LowerApplied27X9 : highNormUpperX LowerApplied27 9 = LowerApplied27Rows 9 := by decide +kernel
theorem LowerApplied27X10 : highNormUpperX LowerApplied27 10 = LowerApplied27Rows 10 := by decide +kernel
theorem LowerApplied27X11 : highNormUpperX LowerApplied27 11 = LowerApplied27Rows 11 := by decide +kernel
theorem LowerApplied27X12 : highNormUpperX LowerApplied27 12 = LowerApplied27Rows 12 := by decide +kernel
theorem LowerApplied27X13 : highNormUpperX LowerApplied27 13 = LowerApplied27Rows 13 := by decide +kernel
theorem LowerApplied27X14 : highNormUpperX LowerApplied27 14 = LowerApplied27Rows 14 := by decide +kernel
theorem LowerApplied27X15 : highNormUpperX LowerApplied27 15 = LowerApplied27Rows 15 := by decide +kernel
theorem LowerApplied27X16 : highNormUpperX LowerApplied27 16 = LowerApplied27Rows 16 := by decide +kernel
theorem LowerApplied27X17 : highNormUpperX LowerApplied27 17 = LowerApplied27Rows 17 := by decide +kernel
theorem LowerApplied27X18 : highNormUpperX LowerApplied27 18 = LowerApplied27Rows 18 := by decide +kernel
theorem LowerApplied27X19 : highNormUpperX LowerApplied27 19 = LowerApplied27Rows 19 := by decide +kernel
theorem LowerApplied27_rows (x : Fin 20) : highNormUpperX LowerApplied27 x = LowerApplied27Rows x := by
  fin_cases x
  · exact LowerApplied27X0
  · exact LowerApplied27X1
  · exact LowerApplied27X2
  · exact LowerApplied27X3
  · exact LowerApplied27X4
  · exact LowerApplied27X5
  · exact LowerApplied27X6
  · exact LowerApplied27X7
  · exact LowerApplied27X8
  · exact LowerApplied27X9
  · exact LowerApplied27X10
  · exact LowerApplied27X11
  · exact LowerApplied27X12
  · exact LowerApplied27X13
  · exact LowerApplied27X14
  · exact LowerApplied27X15
  · exact LowerApplied27X16
  · exact LowerApplied27X17
  · exact LowerApplied27X18
  · exact LowerApplied27X19
theorem LowerApplied27_bound : highNormUpper LowerApplied27 ≤ 5583808878356014 :=
  highNormUpper_le_of_rows LowerApplied27 LowerApplied27Rows 5583808878356014 LowerApplied27_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
