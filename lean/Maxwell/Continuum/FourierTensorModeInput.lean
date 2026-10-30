import Maxwell.Continuum.FourierTensorGeneratedWorkspace
import Maxwell.Continuum.FourierTensorCompiled

/-! The tensor compiler consumes the literal finite calibrated mode.
Its frequency and amplitude bounds follow from the mode norm and integer
frequency enclosure; no analytic approximation premise is introduced. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
open Maxwell.Cost RationalDataflow PartArray Calibration
open scoped BigOperators
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def frequency (M L R : ℕ) (r : Fin (RowArithmetic.rowCount R)) : Fin 3→ℚ :=
  Supercell.templateFrequency M (L:ℚ) (RowArithmetic.rowAlias R r)
def amplitude (M A P R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) : ComplexDyadic P :=
  roundFourierCoefficient P (Supercell.physicalCoefficientData M A (GlobalPower.tableData R a))
    (RowArithmetic.rowAlias R r) j
def componentPayload (M A L R P Q N : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3) : List Bool :=
  Profile.realComponentPayload (frequency M L R) (amplitude M A P R a j) Q N

theorem frequency_bound (M L R Q : ℕ) [NeZero M] (h : L*R≤2*M*Q)
    (r : Fin (RowArithmetic.rowCount R)) (i : Fin 3) : |frequency M L R r i|≤Q := by
  apply Supercell.templateFrequency_bound M (L:ℚ) R Q
  · rw [abs_of_nonneg (by positivity : (0:ℚ)≤L)]
    exact_mod_cast h
  · exact (PeriodicSampling.Product.mem_frequencyCube R _).mpr
      (arrayAlias_mem R ((RowArithmetic.rowEquiv R).symm r))

theorem amplitude_norm (M A P R : ℕ) [NeZero M] (a : Table (2*aliasArraySize R))
    (h : ‖(GlobalPower.tableData R a).value‖≤2) (j : Fin 3) (r : Fin (RowArithmetic.rowCount R)) :
    ‖complexDyadicValue (amplitude M A P R a j r)‖≤6 := by
  have hm := Supercell.physicalCoefficientData_norm M A (GlobalPower.tableData R a)
  have hc := roundFourierCoefficient_norm P (Supercell.physicalCoefficientData M A (GlobalPower.tableData R a))
    (RowArithmetic.rowAlias R r) j
  change ‖complexDyadicValue (amplitude M A P R a j r)‖≤
    ‖(Supercell.physicalCoefficientData M A (GlobalPower.tableData R a)).value‖+2 at hc
  linarith only [hc,hm,h]

theorem amplitude_mass (M A P R E : ℕ) [NeZero M] (a : Table (2*aliasArraySize R))
    (h : ‖(GlobalPower.tableData R a).value‖≤2) (hm : (6:ℝ)*RowArithmetic.rowCount R≤(2:ℝ)^E)
    (j : Fin 3) : (∑r,‖complexDyadicValue (amplitude M A P R a j r)‖)≤(2:ℝ)^E := by
  apply le_trans (Finset.sum_le_sum (fun r _ => amplitude_norm M A P R a h j r))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hm

#print axioms amplitude_mass
#print axioms frequency_bound
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeAllocation
