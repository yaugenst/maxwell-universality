import Maxwell.Certificate.AppliedWitness.LowerApplied4
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia AppliedWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def LowerApplied04Rows : Fin 20 → ℤ := ![40499567313631, 226364950601512, 257087753312471, 300939054843311, 355771633879726, 81643657948307, 429722702644699, 432804276699580, 426570786520258, 412758753614285, 85335677031209, 443360261214678, 437162044558623, 422267645147657, 399581339071181, 72680092945785, 305986731897688, 253747442739500, 216303921077054, 195281865012106]
theorem LowerApplied04X0 : highNormUpperX LowerApplied4 0 = LowerApplied04Rows 0 := by decide +kernel
theorem LowerApplied04X1 : highNormUpperX LowerApplied4 1 = LowerApplied04Rows 1 := by decide +kernel
theorem LowerApplied04X2 : highNormUpperX LowerApplied4 2 = LowerApplied04Rows 2 := by decide +kernel
theorem LowerApplied04X3 : highNormUpperX LowerApplied4 3 = LowerApplied04Rows 3 := by decide +kernel
theorem LowerApplied04X4 : highNormUpperX LowerApplied4 4 = LowerApplied04Rows 4 := by decide +kernel
theorem LowerApplied04X5 : highNormUpperX LowerApplied4 5 = LowerApplied04Rows 5 := by decide +kernel
theorem LowerApplied04X6 : highNormUpperX LowerApplied4 6 = LowerApplied04Rows 6 := by decide +kernel
theorem LowerApplied04X7 : highNormUpperX LowerApplied4 7 = LowerApplied04Rows 7 := by decide +kernel
theorem LowerApplied04X8 : highNormUpperX LowerApplied4 8 = LowerApplied04Rows 8 := by decide +kernel
theorem LowerApplied04X9 : highNormUpperX LowerApplied4 9 = LowerApplied04Rows 9 := by decide +kernel
theorem LowerApplied04X10 : highNormUpperX LowerApplied4 10 = LowerApplied04Rows 10 := by decide +kernel
theorem LowerApplied04X11 : highNormUpperX LowerApplied4 11 = LowerApplied04Rows 11 := by decide +kernel
theorem LowerApplied04X12 : highNormUpperX LowerApplied4 12 = LowerApplied04Rows 12 := by decide +kernel
theorem LowerApplied04X13 : highNormUpperX LowerApplied4 13 = LowerApplied04Rows 13 := by decide +kernel
theorem LowerApplied04X14 : highNormUpperX LowerApplied4 14 = LowerApplied04Rows 14 := by decide +kernel
theorem LowerApplied04X15 : highNormUpperX LowerApplied4 15 = LowerApplied04Rows 15 := by decide +kernel
theorem LowerApplied04X16 : highNormUpperX LowerApplied4 16 = LowerApplied04Rows 16 := by decide +kernel
theorem LowerApplied04X17 : highNormUpperX LowerApplied4 17 = LowerApplied04Rows 17 := by decide +kernel
theorem LowerApplied04X18 : highNormUpperX LowerApplied4 18 = LowerApplied04Rows 18 := by decide +kernel
theorem LowerApplied04X19 : highNormUpperX LowerApplied4 19 = LowerApplied04Rows 19 := by decide +kernel
theorem LowerApplied04_rows (x : Fin 20) : highNormUpperX LowerApplied4 x = LowerApplied04Rows x := by
  fin_cases x
  · exact LowerApplied04X0
  · exact LowerApplied04X1
  · exact LowerApplied04X2
  · exact LowerApplied04X3
  · exact LowerApplied04X4
  · exact LowerApplied04X5
  · exact LowerApplied04X6
  · exact LowerApplied04X7
  · exact LowerApplied04X8
  · exact LowerApplied04X9
  · exact LowerApplied04X10
  · exact LowerApplied04X11
  · exact LowerApplied04X12
  · exact LowerApplied04X13
  · exact LowerApplied04X14
  · exact LowerApplied04X15
  · exact LowerApplied04X16
  · exact LowerApplied04X17
  · exact LowerApplied04X18
  · exact LowerApplied04X19
theorem LowerApplied04_bound : highNormUpper LowerApplied4 ≤ 5795870158073261 :=
  highNormUpper_le_of_rows LowerApplied4 LowerApplied04Rows 5795870158073261 LowerApplied04_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
