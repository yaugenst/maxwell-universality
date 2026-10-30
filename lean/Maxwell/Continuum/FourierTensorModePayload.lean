import Maxwell.Continuum.FourierTensorModeInput
import Maxwell.Continuum.CalibrationGlobalNorm

/-! The executable product order of calibration aliases gives exactly
the declared frequency-cube coefficient sums and output bytes. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration FreeFiber
open scoped BigOperators
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem sum_rows {α : Type*} [AddCommMonoid α] (R : ℕ) (f : Alias→α) :
    (∑r : Fin (RowArithmetic.rowCount R),f (RowArithmetic.rowAlias R r))=
      ∑ν∈PeriodicSampling.Product.frequencyCube R,f ν := by
  classical
  let e := (RowArithmetic.rowEquiv R).symm.trans (GlobalPower.cubeEquiv R)
  have h := e.sum_comp (fun ν => f ν.1)
  exact h.trans (Finset.sum_coe_sort _ _)

theorem coefficient_reindex {B : ℕ} (R Q N : ℕ) (q : Alias→Fin 3→ℚ)
    (a : Alias→ComplexDyadic B) (j : Fin 3→Fin (waveDegree (8*Q) N)) :
    fourierTensorCoefficient Finset.univ (fun r => q (RowArithmetic.rowAlias R r))
      (fun r => a (RowArithmetic.rowAlias R r)) Q N j=
      fourierTensorCoefficient (PeriodicSampling.Product.frequencyCube R) q a Q N j := by
  apply Prod.ext
  · exact congrArg Dyadic.mk (sum_rows R (fun ν =>
      (complexDyadicMul (a ν) (tensorWaveCoefficient (q ν) Q N j)).1.numerator))
  · exact congrArg Dyadic.mk (sum_rows R (fun ν =>
      (complexDyadicMul (a ν) (tensorWaveCoefficient (q ν) Q N j)).2.numerator))

theorem finalData_reindex {B : ℕ} (R Q N : ℕ) (q : Alias→Fin 3→ℚ) (a : Alias→ComplexDyadic B) :
    finalData Finset.univ (fun r => q (RowArithmetic.rowAlias R r))
      (fun r => a (RowArithmetic.rowAlias R r)) Q N=
      finalData (PeriodicSampling.Product.frequencyCube R) q a Q N := by
  simp only [finalData,coefficient_reindex]

theorem vectorBits_reindex {B : ℕ} (R Q N : ℕ) (q : Alias→Fin 3→ℚ)
    (a : Fin 3→Alias→ComplexDyadic B) :
    realFinalVectorBits Finset.univ (fun r => q (RowArithmetic.rowAlias R r))
      (fun j r => a j (RowArithmetic.rowAlias R r)) Q N=
      realFinalVectorBits (PeriodicSampling.Product.frequencyCube R) q a Q N := by
  simp only [realFinalVectorBits,realFinalVectorData,finalVectorData,finalData_reindex]

theorem vectorBits_components (M A L R P Q N : ℕ) (a : Table (2*aliasArraySize R)) :
    realFinalVectorBits (PeriodicSampling.Product.frequencyCube R) (Supercell.templateFrequency M (L:ℚ))
      (fun j ν => roundFourierCoefficient P (Supercell.physicalCoefficientData M A (GlobalPower.tableData R a)) ν j) Q N=
      Codec.nat (P+(waveWorkBits (8*Q) N+waveWorkBits (8*Q) N+waveWorkBits (8*Q) N))++
        Codec.nat (3*(waveDegree (8*Q) N)^3)++
        componentPayload M A L R P Q N a 0++componentPayload M A L R P Q N a 1++
        componentPayload M A L R P Q N a 2 := by
  rw [←vectorBits_reindex R Q N]
  exact Profile.realFinalVectorBits_components (frequency M L R) (amplitude M A P R a) Q N

#print axioms vectorBits_components
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
