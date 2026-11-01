import Maxwell.Continuum.ParameterSourceInitialize

/-! Actual source counts are copied, the condition/error operands are
computed, and the source logarithm is measured before the outer search. -/
namespace Maxwell.Continuum.Parameters.SourcePrepare
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def ports : Finset ℕ := SourceBudgetMachine.outputs∪{2200}
def code (κ η e : ℕ) : Code := .seq SourceInitialize.code
  (.seq (SourceBudgetMachine.code κ η e) SourceLogMachine.code)
def work : Finset ℕ := SourceInitialize.work∪SourceBudgetMachine.workspace∪SourceLogMachine.workspace
def initialWidth (n m circuit side sites : ℕ) : ℕ := 32*(SourceInitialize.inputWidth n m circuit side sites+1)
def budgetWidth (κ η e n m circuit side sites : ℕ) : ℕ :=
  SourceBudgetMachine.width κ η e (initialWidth n m circuit side sites)
def budgetValues (κ η e n m circuit side sites : ℕ) : ℕ→ℕ :=
  NatAssign.values (SourceBudgetMachine.instructions κ η e) (SourceInitialize.values n m circuit side sites)
def values (κ η e n m circuit side sites : ℕ) : ℕ→ℕ :=
  Function.update (budgetValues κ η e n m circuit side sites) 2200 (inputLog m)
def cost (κ η e n m circuit side sites : ℕ) : ℕ :=
  3000*8^5*(SourceInitialize.inputWidth n m circuit side sites+2)^2+
    (SourceBudgetMachine.cost κ η e (initialWidth n m circuit side sites)+
      SourceLogMachine.cost (budgetWidth κ η e n m circuit side sites))

theorem budget_zero (κ η e n m circuit side sites : ℕ) :
    budgetValues κ η e n m circuit side sites 2200=0 := by
  rw [budgetValues,NatAssign.values_outside SourceBudgetMachine.ids _ (SourceBudgetMachine.valid κ η e)
    _ _ (by decide)]
  rfl

theorem fields (κ η e n m circuit side sites : ℕ) :
    let r:=values κ η e n m circuit side sites
    r 2200=inputLog m ∧ r 2201=minimumLengthExponent e ∧ r 2210=2^e ∧ r 2211=m ∧ r 2212=sites ∧
    r 2213=SourceBudgetMachine.condition m circuit side κ ∧ r 2214=1 ∧ r 2215=1 ∧
    r 2216=SourceBudgetMachine.errorDen n m circuit side η ∧
    (∀i∈({2217,2218,2219}:Finset ℕ),r i=2^54*129*side) := by
  have result:=SourceBudgetMachine.result_values κ η e (SourceInitialize.values n m circuit side sites)
  have inputs:=SourceInitialize.fields n m circuit side sites
  dsimp only at result ⊢
  simp only [inputs.1,inputs.2.1,inputs.2.2.1,inputs.2.2.2.1,inputs.2.2.2.2] at result
  refine ⟨rfl,result.1,result.2.1,result.2.2.1,result.2.2.2.1,result.2.2.2.2.1,
    result.2.2.2.2.2.1,result.2.2.2.2.2.2.1,result.2.2.2.2.2.2.2.1,?_⟩
  intro i hi
  have different : i≠2200 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega
  simpa only [values,Function.update_of_ne different,budgetValues] using result.2.2.2.2.2.2.2.2 i hi

theorem executes (κ η e n m circuit side sites : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (wn : Word s.val 500 n) (wm : Word s.val 501 m) (wc : Word s.val 503 circuit)
    (wq : Word s.val 1200 side) (wj : Word s.val 1209 sites)
    (fresh : ∀i∈SourceLogMachine.ids,Blank s.val i) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape (code κ η e) steps s t ∧ steps≤cost κ η e n m circuit side sites ∧
      NatAssign.Bank ports (values κ η e n m circuit side sites) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c₀,a,e₀,h₀,ba,wa,za,f₀⟩:=SourceInitialize.executes n m circuit side sites input tape s
    wn wm wc wq wj fresh scratch
  obtain ⟨c₁,b,e₁,h₁,bb,wb,zb,f₁⟩:=SourceBudgetMachine.executes κ η e (initialWidth n m circuit side sites)
    (SourceInitialize.values n m circuit side sites) (fun i hi=>wa i (Finset.mem_union_left _ hi))
    input tape a (fun i hi=>ba i (Finset.mem_union_left _ hi)) za
  change NatAssign.Bank SourceBudgetMachine.ids (budgetValues κ η e n m circuit side sites) b.val at bb
  have bank : NatAssign.Bank SourceLogMachine.ids (budgetValues κ η e n m circuit side sites) b.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact bb i hi
    · have eq : i=2200 := Finset.mem_singleton.mp hi
      subst i
      rw [budget_zero]
      exact RationalAccumulator.word_of_eq (f₁.tapes 2200 (by decide)) (ba 2200 (by decide))
  have width : ∀i∈SourceLogMachine.ids,(budgetValues κ η e n m circuit side sites i).bits.length≤
      budgetWidth κ η e n m circuit side sites := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact wb i hi
    · have eq : i=2200 := Finset.mem_singleton.mp hi
      subst i
      simp only [budget_zero,show (0:ℕ).bits.length=0 by decide,Nat.zero_le]
  obtain ⟨c₂,t,e₂,h₂,word,zt,f₂⟩:=SourceLogMachine.executes (budgetValues κ η e n m circuit side sites)
    (budgetWidth κ η e n m circuit side sites) width input tape b bank zb
  have sourceCount : budgetValues κ η e n m circuit side sites 2301=m := by
    rw [budgetValues,SourceBudgetMachine.result_inputs κ η e _ 2301 (by decide)]
    exact (SourceInitialize.fields n m circuit side sites).2.1
  refine ⟨c₀+(c₁+c₂),t,e₀.seq (e₁.seq e₂),Nat.add_le_add h₀ (Nat.add_le_add h₁ h₂),?_,zt,
    (f₀.mono (by intro i hi;exact Finset.mem_union_left _ (Finset.mem_union_left _ hi))).trans
      ((f₁.mono (by intro i hi;exact Finset.mem_union_left _ (Finset.mem_union_right _ hi))).trans
        (f₂.mono Finset.subset_union_right))⟩
  intro i hi
  by_cases same : i=2200
  · subst i
    simpa only [values,Function.update_self,sourceCount] using word
  · have ho : i∈SourceBudgetMachine.outputs := by
      rcases Finset.mem_union.mp hi with hi|hi
      · exact hi
      · exact False.elim (same (Finset.mem_singleton.mp hi))
    rw [values,Function.update_of_ne same]
    apply RationalAccumulator.word_of_eq (f₂.tapes i ?_) (bb i (Finset.mem_union_right _ ho))
    simp only [SourceBudgetMachine.outputs,Finset.mem_insert,Finset.mem_singleton] at ho
    simp only [SourceLogMachine.workspace,Finset.mem_insert,Finset.mem_singleton]
    omega

#print axioms executes
end Maxwell.Continuum.Parameters.SourcePrepare
