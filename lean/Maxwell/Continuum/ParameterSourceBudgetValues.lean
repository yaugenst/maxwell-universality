import Maxwell.Continuum.ParameterSourceBudgetData

namespace Maxwell.Continuum.Parameters.SourceBudgetMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def afterPowers (κ η : ℕ) (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (Function.update v 2310 ((v 2301)^(κ+1))) 2311 ((v 2301)^η)
def afterCondition (κ η : ℕ) (v : ℕ→ℕ) : ℕ→ℕ :=
  NatAssign.values conditionInstructions (afterPowers κ η v)
def afterError (κ η : ℕ) (v : ℕ→ℕ) : ℕ→ℕ :=
  NatAssign.values errorInstructions (afterCondition κ η v)

theorem powers_values (κ η : ℕ) (v : ℕ→ℕ) :
    NatAssign.values (powers κ η) v=afterPowers κ η v := by
  rw [powers,NatAssign.values_append,NatAssign.power_values _ _ _ (by decide),
    NatAssign.power_values _ _ _ (by decide)]
  rfl

theorem afterPowers_input (κ η : ℕ) (v : ℕ→ℕ) (i : ℕ) (hi : i∈inputs) :
    afterPowers κ η v i=v i := by
  have bounds:=Finset.mem_Icc.mp hi
  simp only [afterPowers,Function.update_of_ne (show i≠2311 by omega),
    Function.update_of_ne (show i≠2310 by omega)]

theorem afterCondition_input (κ η : ℕ) (v : ℕ→ℕ) (i : ℕ) (hi : i∈inputs) :
    afterCondition κ η v i=v i := by
  rw [afterCondition,condition_preserves _ _ (Or.inl hi),afterPowers_input κ η v i hi]

theorem afterCondition_value (κ η : ℕ) (v : ℕ→ℕ) :
    afterCondition κ η v 2326=condition (v 2301) (v 2302) (v 2303) κ := by
  rw [afterCondition,condition_values]
  simp [afterPowers,condition]

theorem afterError_input (κ η : ℕ) (v : ℕ→ℕ) (i : ℕ) (hi : i∈inputs) :
    afterError κ η v i=v i := by
  rw [afterError,error_preserves _ _ (Or.inl hi),afterCondition_input κ η v i hi]

theorem afterError_condition (κ η : ℕ) (v : ℕ→ℕ) :
    afterError κ η v 2326=condition (v 2301) (v 2302) (v 2303) κ := by
  rw [afterError,error_preserves _ _ (Or.inr rfl),afterCondition_value]

theorem afterError_value (κ η : ℕ) (v : ℕ→ℕ) :
    afterError κ η v 2331=errorDen (v 2300) (v 2301) (v 2302) (v 2303) η := by
  rw [afterError,error_values]
  rw [afterCondition_input κ η v 2300 (by decide),afterCondition_input κ η v 2301 (by decide),
    afterCondition_input κ η v 2302 (by decide),afterCondition_input κ η v 2303 (by decide)]
  have power : afterCondition κ η v 2311=(v 2301)^η := by
    rw [afterCondition,condition_preserves _ _ (Or.inr (Or.inr rfl))]
    simp [afterPowers]
  rw [power]
  rfl

theorem result_inputs (κ η e : ℕ) (v : ℕ→ℕ) (i : ℕ) (hi : i∈inputs) :
    NatAssign.values (instructions κ η e) v i=v i := by
  simp only [instructions,NatAssign.values_append,powers_values]
  change NatAssign.values (outputInstructions e) (afterError κ η v) i=v i
  rw [NatAssign.values_preserves (outputInstructions e) (afterError κ η v) i]
  · exact afterError_input κ η v i hi
  · intro a ha
    have bounds:=Finset.mem_Icc.mp hi
    simp only [outputInstructions,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [NatAssign.Instruction.target];omega

theorem result_values (κ η e : ℕ) (v : ℕ→ℕ) :
    let r:=NatAssign.values (instructions κ η e) v
    r 2201=minimumLengthExponent e ∧ r 2210=2^e ∧ r 2211=v 2301 ∧ r 2212=v 2304 ∧
    r 2213=condition (v 2301) (v 2302) (v 2303) κ ∧ r 2214=1 ∧ r 2215=1 ∧
    r 2216=errorDen (v 2300) (v 2301) (v 2302) (v 2303) η ∧
    (∀i∈({2217,2218,2219} : Finset ℕ),r i=2^54*129*v 2303) := by
  dsimp only
  simp only [instructions,NatAssign.values_append,powers_values]
  change let r:=NatAssign.values (outputInstructions e) (afterError κ η v);_
  have h1:=afterError_input κ η v 2301 (by decide)
  have h3:=afterError_input κ η v 2303 (by decide)
  have h4:=afterError_input κ η v 2304 (by decide)
  have hK:=afterError_condition κ η v
  have hE:=afterError_value κ η v
  simp only [outputInstructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]
  simp
  exact ⟨h1,h4,hK,hE,h3⟩

#print axioms result_values
end Maxwell.Continuum.Parameters.SourceBudgetMachine
