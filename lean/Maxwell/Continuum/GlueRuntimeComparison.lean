import Maxwell.Continuum.GlueRuntimeSetup

/-! Exact threshold comparison for the fixed glue evaluator. The stored
precision and the computed Taylor count survive the comparison unchanged. -/
namespace Maxwell.Continuum.GlueMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def comparisonExtra : Finset ℕ := GlueMachine.extra∪{607,640,641,642,643}
def comparisonValues (a b N : ℕ) : ℕ→ℕ :=
  NatAssign.values (SelectedParameters.Compare.prepare 608 609 600 601) (setupValues a b N)
def comparisonCode : Code := SelectedParameters.Compare.code 608 609 600 601
def setupWidth (W : ℕ) : ℕ := 2^15*(W+1)

theorem comparison_ids : SelectedParameters.Compare.ids comparisonExtra=ids := by
  ext i
  simp only [SelectedParameters.Compare.ids,comparisonExtra,ids,GlueMachine.ids,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem comparisonExtra_ge (i : ℕ) (hi : i∈comparisonExtra) : 40 ≤ i := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact GlueMachine.extra_ge i hi
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem comparisonValues_core (a b N i : ℕ) (hi : i∈GlueMachine.ids) :
    comparisonValues a b N i=GlueMachine.comparedValues a b N i := by
  have he := SelectedParameters.Compare.prepared 608 609 600 601
    (by decide) (by decide) (by decide) (by decide) (setupValues a b N)
  have he' := SelectedParameters.Compare.prepared 608 609 600 601
    (by decide) (by decide) (by decide) (by decide) (GlueMachine.initializedValues a b N)
  simp only [comparisonValues,GlueMachine.comparedValues,he,he',Function.update_apply]
  rw [setupValues_core a b N 608 (by decide),setupValues_core a b N 609 (by decide),
    setupValues_core a b N 600 (by decide),setupValues_core a b N 601 (by decide),
    setupValues_core a b N i hi]

theorem comparisonValues_saved (a b N : ℕ) :
    comparisonValues a b N 640=N ∧ comparisonValues a b N 641=GlueMachine.order N ∧
    comparisonValues a b N 607=0 := by
  simp only [comparisonValues,SelectedParameters.Compare.prepare,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
  simp (disch := decide) only [Function.update_of_ne]
  refine ⟨setupValues_precision a b N,setupValues_order a b N,?_⟩
  simp [setupValues,setup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,initialValues,GlueMachine.initialValues]

theorem comparisonValues_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (i : ℕ) (hi : i∈ids) :
    (comparisonValues a b N i).bits.length≤setupWidth W := by
  have he := SelectedParameters.Compare.prepared 608 609 600 601
    (by decide) (by decide) (by decide) (by decide) (setupValues a b N)
  have h0 := setup_width a b N W ha hb hN hW 608 (by decide)
  have h1 := setup_width a b N W ha hb hN hW 609 (by decide)
  have h2 := setup_width a b N W ha hb hN hW 600 (by decide)
  have h3 := setup_width a b N W ha hb hN hW 601 (by decide)
  have h4 := setup_width a b N W ha hb hN hW i hi
  simp only [comparisonValues,he,Function.update_apply]
  split_ifs <;> assumption

theorem comparison_executes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (hb0 : 0<b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (setupValues a b N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape comparisonCode cost s t ∧
      cost≤2^25*(setupWidth W+2)^2 ∧
      t.val.registers 35=decide ((1:ℚ)/((N:ℚ)+1)<(a:ℚ)/b) ∧
      NatAssign.Bank ids (comparisonValues a b N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have hbank : NatAssign.Bank (SelectedParameters.Compare.ids comparisonExtra) (setupValues a b N) s.val := by
    rwa [comparison_ids]
  have h608 := setupValues_core a b N 608 (by decide)
  have h609 := setupValues_core a b N 609 (by decide)
  have h600 := setupValues_core a b N 600 (by decide)
  have h601 := setupValues_core a b N 601 (by decide)
  simp [GlueMachine.initializedValues,GlueMachine.initialValues] at h608 h609 h600 h601
  obtain ⟨cost,t,ex,hcost,sg,bt,zt,ft⟩ := SelectedParameters.Compare.executes comparisonExtra comparisonExtra_ge
    608 609 600 601 (by decide) (by decide) (by decide) (by decide) (setupValues a b N) (setupWidth W)
    (fun i hi => setup_width a b N W ha hb hN hW i (by rwa [comparison_ids] at hi))
    (by rw [h609];omega) (by rw [h601];exact hb0)
    (by rw [setupValues_core a b N 35 (by decide)];rfl)
    (by rw [setupValues_core a b N 36 (by decide)];rfl) input tape s hbank hz
  refine ⟨cost,t,ex,?_,?_,?_,zt,?_⟩
  · nlinarith only [hcost]
  · simpa only [h608,h609,h600,h601,Nat.cast_add,Nat.cast_one] using sg
  · change NatAssign.Bank _ (comparisonValues a b N) t.val at bt
    simpa only [comparison_ids] using bt
  · exact ft.mono (by decide)

#print axioms comparison_executes
end Maxwell.Continuum.GlueMachine.Runtime
