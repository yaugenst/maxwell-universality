import Maxwell.Certificate.AppliedWitness.LowerApplied0
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied00Rows : Fin 20 → ℤ := ![40407228444305, 225856149376526, 256500449084282, 300241297614338, 354950914525844, 81455539859973, 428719148364183, 431774296788378, 425555747996095, 411800107367339, 85138442058848, 442322028277012, 436122350786133, 421262946917741, 398656766941626, 72510995009158, 305291723926890, 253167272403726, 215807151675694, 194836513527422]
theorem LowerApplied00X0 : highNormUpperX LowerApplied0 0 = LowerApplied00Rows 0 := by decide +kernel
theorem LowerApplied00X1 : highNormUpperX LowerApplied0 1 = LowerApplied00Rows 1 := by decide +kernel
theorem LowerApplied00X2 : highNormUpperX LowerApplied0 2 = LowerApplied00Rows 2 := by decide +kernel
theorem LowerApplied00X3 : highNormUpperX LowerApplied0 3 = LowerApplied00Rows 3 := by decide +kernel
theorem LowerApplied00X4 : highNormUpperX LowerApplied0 4 = LowerApplied00Rows 4 := by decide +kernel
theorem LowerApplied00X5 : highNormUpperX LowerApplied0 5 = LowerApplied00Rows 5 := by decide +kernel
theorem LowerApplied00X6 : highNormUpperX LowerApplied0 6 = LowerApplied00Rows 6 := by decide +kernel
theorem LowerApplied00X7 : highNormUpperX LowerApplied0 7 = LowerApplied00Rows 7 := by decide +kernel
theorem LowerApplied00X8 : highNormUpperX LowerApplied0 8 = LowerApplied00Rows 8 := by decide +kernel
theorem LowerApplied00X9 : highNormUpperX LowerApplied0 9 = LowerApplied00Rows 9 := by decide +kernel
theorem LowerApplied00X10 : highNormUpperX LowerApplied0 10 = LowerApplied00Rows 10 := by decide +kernel
theorem LowerApplied00X11 : highNormUpperX LowerApplied0 11 = LowerApplied00Rows 11 := by decide +kernel
theorem LowerApplied00X12 : highNormUpperX LowerApplied0 12 = LowerApplied00Rows 12 := by decide +kernel
theorem LowerApplied00X13 : highNormUpperX LowerApplied0 13 = LowerApplied00Rows 13 := by decide +kernel
theorem LowerApplied00X14 : highNormUpperX LowerApplied0 14 = LowerApplied00Rows 14 := by decide +kernel
theorem LowerApplied00X15 : highNormUpperX LowerApplied0 15 = LowerApplied00Rows 15 := by decide +kernel
theorem LowerApplied00X16 : highNormUpperX LowerApplied0 16 = LowerApplied00Rows 16 := by decide +kernel
theorem LowerApplied00X17 : highNormUpperX LowerApplied0 17 = LowerApplied00Rows 17 := by decide +kernel
theorem LowerApplied00X18 : highNormUpperX LowerApplied0 18 = LowerApplied00Rows 18 := by decide +kernel
theorem LowerApplied00X19 : highNormUpperX LowerApplied0 19 = LowerApplied00Rows 19 := by decide +kernel
theorem LowerApplied00_rows (x : Fin 20) : highNormUpperX LowerApplied0 x = LowerApplied00Rows x := by
  fin_cases x
  · exact LowerApplied00X0
  · exact LowerApplied00X1
  · exact LowerApplied00X2
  · exact LowerApplied00X3
  · exact LowerApplied00X4
  · exact LowerApplied00X5
  · exact LowerApplied00X6
  · exact LowerApplied00X7
  · exact LowerApplied00X8
  · exact LowerApplied00X9
  · exact LowerApplied00X10
  · exact LowerApplied00X11
  · exact LowerApplied00X12
  · exact LowerApplied00X13
  · exact LowerApplied00X14
  · exact LowerApplied00X15
  · exact LowerApplied00X16
  · exact LowerApplied00X17
  · exact LowerApplied00X18
  · exact LowerApplied00X19
theorem LowerApplied00_bound : highNormUpper LowerApplied0 ≤ 5782377070945513 :=
  highNormUpper_le_of_rows LowerApplied0 LowerApplied00Rows 5782377070945513 LowerApplied00_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
