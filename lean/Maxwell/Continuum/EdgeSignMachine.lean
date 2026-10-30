import Maxwell.Continuum.DefinitenessExpressionMachine

/-! One fixed Boolean program tests the actual 24 by 24 rational edge matrix.
Its entries are input words; the fixed circuit constant is independent of
the matrix, field accuracy, and source instance size. -/

namespace Maxwell.Continuum.Calibration.EdgeSignMachine

open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured ExpressionDefiniteness

def entryIndex (i j : Fin 24) : ℕ := 24*i.val+j.val

theorem entryIndex_lt (i j : Fin 24) : entryIndex i j<576 := by
  unfold entryIndex
  have hi := i.isLt
  have hj := j.isLt
  omega

def expressions : Matrix (Fin 24) (Fin 24) RationalExpression :=
  fun i j => .binary .sub .zero (.input (entryIndex i j))

def inputMatrix (v : ℕ → Parts) : Matrix (Fin 24) (Fin 24) Parts := fun i j => v (entryIndex i j)

theorem expressions_below : Below expressions 577 := by
  intro i j
  change True ∧ entryIndex i j<577
  exact ⟨trivial,lt_trans (entryIndex_lt i j) (by decide)⟩

theorem expressions_evaluate (v : ℕ → Parts) :
    ExpressionDefiniteness.evaluate expressions v=RawDefiniteness.negate (inputMatrix v) := rfl

attribute [local irreducible] ExpressionDefiniteness.extent ExpressionDefiniteness.control
  ExpressionDefiniteness.costConstant

def bankSize : ℕ := 577+extent expressions
def signControl : Control := control expressions 576 577
def signCostConstant : ℕ := costConstant expressions 576 577

theorem entryIndex_mem (i j : Fin 24) : entryIndex i j∈Finset.range bankSize := by
  apply Finset.mem_range.mpr
  exact lt_of_lt_of_le (lt_trans (entryIndex_lt i j) (by decide : 576<577)) (Nat.le_add_right _ _)

theorem expressions_safe (v : ℕ → Parts) (hv : Good (Finset.range bankSize) v) : Safe expressions v := by
  intro i j
  exact ⟨trivial,hv (entryIndex i j) (entryIndex_mem i j)⟩

theorem sign_computes (v : ℕ → Parts) (W : ℕ) (hw : WidthBank (Finset.range bankSize) W v)
    (hg : Good (Finset.range bankSize) v) (input : List Bool) (tape : ℕ → Bool) (st : Store)
    (hst : Ready (Finset.range bankSize) v st) :
    ∃ cost t output,
      (runPriced (signControl.code.compile.next input tape)
        (signCostConstant*(W+1)^2+1) st.val).finished=some (t.place signControl.code.size) ∧
      (runPriced (signControl.code.compile.next input tape)
        (signCostConstant*(W+1)^2+1) st.val).instructions=cost ∧
      cost≤signCostConstant*(W+1)^2 ∧ Ready (Finset.range bankSize) output t ∧
      (output 576).value=if negativeTest (RawDefiniteness.values (inputMatrix v)) then 1 else 0 := by
  obtain ⟨cost,t,output,hrun,hcharged,hcost,hready,hresult⟩ := control_computes
    expressions 576 577 (by decide) expressions_below v W hw hg (expressions_safe v hg) input tape st hst
  refine ⟨cost,t,output,hrun,hcharged,hcost,hready,?_⟩
  rw [expressions_evaluate] at hresult
  have hvalid : RawDefiniteness.Valid (inputMatrix v) :=
    fun i j => hg (entryIndex i j) (entryIndex_mem i j)
  change output 576=Parts.literal (if RawDefiniteness.negative (inputMatrix v) then 1 else 0) at hresult
  rw [RawDefiniteness.negative_value _ hvalid] at hresult
  rw [hresult,Parts.literal_value]

#print axioms sign_computes

end Maxwell.Continuum.Calibration.EdgeSignMachine
