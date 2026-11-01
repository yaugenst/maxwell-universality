import Maxwell.Continuum.ParameterBufferMachineWidths

namespace Maxwell.Continuum.Parameters.BufferMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] values

def resetTargets : List ℕ := [2117,2118,2119]++(List.range 32).map (·+2125)
def resetInstructions : List NatAssign.Instruction := resetTargets.map (fun i=>.literal i 0)
def advance : List NatAssign.Instruction := resetInstructions++[.multiply 2121 2115]
def beforeQuotient (D : Data) (k : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (inputs D k) 2117 0) 2118 0

theorem reset_mem (i : ℕ) : i∈resetTargets ↔ i=2117 ∨ i=2118 ∨ i=2119 ∨ 2125 ≤ i ∧ i ≤ 2156 := by
  simp only [resetTargets,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,List.mem_range]
  constructor
  · rintro (h|⟨j,hj,rfl⟩)
    · tauto
    · omega
  · rintro (h|h|h|h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · right;exact ⟨i-2125,by omega,by omega⟩

theorem advance_valid : ∀a∈advance,a.Valid extra := by
  intro a ha
  simp only [advance,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with ha|rfl
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [NatAssign.Instruction.Valid,extra,Finset.mem_union,Finset.mem_Icc,
      Finset.mem_insert,Finset.mem_singleton]
    rw [reset_mem] at hi
    omega
  · simp [NatAssign.Instruction.Valid,extra]

theorem advance_values (D : Data) (k : ℕ) (v : ℕ→ℕ)
    (hv : ∀i∈extra,v i=values D k i) :
    ∀i∈extra,NatAssign.values advance v i=beforeQuotient D (k+1) i := by
  have h15 : v 2115=2^k := by
    rw [hv 2115 (by decide +kernel),input_fields D k 2115 (by decide)]
    simp [inputs]
  have h21 : v 2121=2 := by
    rw [hv 2121 (by decide +kernel),input_fields D k 2121 (by decide)]
    simp [inputs]
  have resets (i : ℕ) : NatAssign.values resetInstructions v i=if i∈resetTargets then 0 else v i :=
    NatAssign.values_literals resetTargets (fun _=>0) v i
  intro i hi
  simp only [advance,NatAssign.values_append,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  rw [resets 2121,resets 2115]
  simp only [reset_mem,show ¬(2121=2117 ∨ 2121=2118 ∨ 2121=2119 ∨ 2125 ≤ 2121 ∧ 2121 ≤ 2156) by decide,
    show ¬(2115=2117 ∨ 2115=2118 ∨ 2115=2119 ∨ 2125 ≤ 2115 ∧ 2115 ≤ 2156) by decide,ite_false,h15,h21]
  by_cases ht : i=2115
  · subst i;simp [beforeQuotient,inputs,pow_succ,Nat.mul_comm]
  rw [Function.update_of_ne ht,resets]
  by_cases hr : i∈resetTargets
  · rw [ite_eq_left hr]
    rw [reset_mem] at hr
    rcases hr with rfl|rfl|rfl|hr
    · simp [beforeQuotient]
    · simp [beforeQuotient]
    · simp [beforeQuotient,inputs]
    · simp only [beforeQuotient,Function.update_of_ne (show i≠2117 by omega),
        Function.update_of_ne (show i≠2118 by omega),inputs]
      repeat' rw [ite_eq_right (by omega)]
  · rw [ite_eq_right hr,hv i hi]
    have hi' := hi
    simp only [extra,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi'
    have hn := (reset_mem i).not.mp hr
    have hsmall : i<2125 := by omega
    rw [input_fields D k i hsmall]
    simp only [beforeQuotient,Function.update_of_ne (show i≠2117 by omega),
      Function.update_of_ne (show i≠2118 by omega),inputs]
    simp only [ite_eq_right ht,ite_eq_right (show i≠2117 by omega),
      ite_eq_right (show i≠2118 by omega)]


theorem quotient_values (D : Data) (k : ℕ) (v : ℕ→ℕ)
    (hv : ∀i∈extra,v i=beforeQuotient D k i) :
    ∀i∈extra,Function.update v 2118 (v 2115/v 2116) i=
      Function.update (inputs D k) 2117 0 i := by
  have hs : v 2115=2^k := by simpa [beforeQuotient,inputs] using hv 2115 (by decide +kernel)
  have hd : v 2116=slowDivisor := by simpa [beforeQuotient,inputs] using hv 2116 (by decide +kernel)
  intro i hi
  by_cases he : i=2118
  · subst i;simp [hs,hd,inputs]
  · rw [Function.update_of_ne he,hv i hi]
    exact Function.update_of_ne he _ _

theorem power_values (D : Data) (k : ℕ) (v : ℕ→ℕ)
    (hv : ∀i∈extra,v i=Function.update (inputs D k) 2117 0 i) :
    ∀i∈extra,Function.update v 2117 (2^(v 2118)) i=inputs D k i := by
  have hq : v 2118=(2^k)/slowDivisor := by simpa [inputs] using hv 2118 (by decide +kernel)
  intro i hi
  by_cases he : i=2117
  · subst i;simp [hq,inputs]
  · rw [Function.update_of_ne he,hv i hi,Function.update_of_ne he]

#print axioms advance_values
#print axioms power_values
end Maxwell.Continuum.Parameters.BufferMachine
