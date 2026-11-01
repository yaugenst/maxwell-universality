import Maxwell.Continuum.ParameterSpacingMachineWidths

namespace Maxwell.Continuum.Parameters.SpacingMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
attribute [local irreducible] values

def advance : List NatAssign.Instruction :=
  [.copy 2007 2031,.multiply 2031 2007,
   .copy 2008 2031,.multiply 2031 2008,
   .copy 2006 2031,.add 2031 2006]++
    (List.range 12).map (fun i => .literal (2020+i) 0)

theorem advance_valid : ∀ a ∈ advance, a.Valid extra := by
  simp [advance,NatAssign.Instruction.Valid,extra,List.mem_range]
  omega

theorem formulas_extra_valid : ∀ a ∈ formulas, a.Valid extra := by
  simp [formulas,NatAssign.Instruction.Valid,extra]

theorem advance_values (D : Data) (k : ℕ) (i : ℕ) (hi : i∈extra) :
    NatAssign.values advance (values D k) i=inputs D (k+1) i := by
  have hcore (j : ℕ) (hj : j≤2019) : values D k j=inputs D k j := input_fields D k j hj
  have h06 := hcore 2006 (by decide)
  have h07 := hcore 2007 (by decide)
  have h08 := hcore 2008 (by decide)
  simp [inputs] at h06 h07 h08
  simp only [extra,Finset.mem_Icc] at hi
  obtain ⟨hlo,hhi⟩ := hi
  interval_cases i
  all_goals simp [advance,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,List.range_succ,h06,h07,h08,
    hcore,inputs,pow_succ,← pow_add,Nat.mul_comm]
  all_goals omega

theorem next_values (D : Data) (k : ℕ) (v : ℕ→ℕ)
    (hv : ∀ i ∈ extra, v i=values D k i) :
    ∀ i ∈ extra, NatAssign.values (advance++formulas) v i=values D (k+1) i := by
  intro i hi
  rw [NatAssign.values_append]
  rw [values]
  apply NatAssign.values_congr extra formulas formulas_extra_valid _ _ _ i hi
  intro j hj
  exact (NatAssign.values_congr extra advance advance_valid v _ hv j hj).trans
    (advance_values D k j hj)

#print axioms next_values

end Maxwell.Continuum.Parameters.SpacingMachine
