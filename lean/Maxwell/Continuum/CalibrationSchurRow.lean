import Maxwell.Continuum.CalibrationSchurExpression
import Maxwell.Continuum.RationalDataflowExpressionRegisters
import Maxwell.Continuum.RationalDataflowExpressionFrame
import Maxwell.Continuum.RationalDataflowPartsCopy

/-! Evaluate a Schur entry from retained raw cells, then copy the computed
parts into its matrix position. One bounded bank serves every row and column. -/
namespace Maxwell.Continuum.Calibration.SchurRow
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PolynomialExpression SchurExpression
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def nodeCount : ℕ := (expression 0 0).nodes
def bank : Finset ℕ := (Finset.Ico 232 384∪Finset.Ico 500 1076)∪Finset.Ico 1200 (1200+nodeCount)
def output (row column : Fin 24) : ℕ := 500+24*row.val+column.val
def result (row column : Fin 24) (v : ℕ→Parts) : ℕ→Parts :=
  let computed:=((expression row column).control 1200).evaluate v
  Function.update computed (output row column) (computed 1200)
def code (row column : Fin 24) : Code :=
  .seq ((expression row column).control 1200).code (partsCopyCode 1200 (output row column))
def width (B : ℕ) : ℕ := 2^(3*nodeCount)*(B+1)
def costBound (B : ℕ) : ℕ := 3*nodeCount*operationCost (width B)+1+stageCost (width B)

theorem nodes (row column : Fin 24) : (expression row column).nodes=nodeCount := rfl

theorem nodeCount_value : nodeCount=171 := rfl

attribute [local irreducible] nodeCount

theorem input_bounds (row column : Fin 24) (i : ℕ) (hi:i∈(expression row column).inputs) :
    232 ≤ i ∧ i<384 := by
  have neighborBound (j : Fin 3) (plus : Bool) :
      240≤neighborRegister row j plus ∧ neighborRegister row j plus<384 := by
    unfold neighborRegister
    split_ifs <;> omega
  simp only [expression,central,block,direction,selected,square,sum3,inputs,
    Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false,false_or] at hi
  have ht:=neighborBound 0 true
  have hf:=neighborBound 0 false
  have ht1:=neighborBound 1 true
  have hf1:=neighborBound 1 false
  have ht2:=neighborBound 2 true
  have hf2:=neighborBound 2 false
  have pol: (BasisForcing.polarization row).val<3 := (BasisForcing.polarization row).isLt
  omega

theorem valid (row column : Fin 24) : ((expression row column).control 1200).Valid bank := by
  apply Control.prepend_valid
  · apply instructions_valid_in
    · intro i hi
      have h:=input_bounds row column i hi
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_Ico.mpr h))
    · intro i lo hi
      exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨lo,by rwa [nodes] at hi⟩)
  · trivial

theorem scratch_mem : 1200∈bank := by
  have h:0<nodeCount:=by rw [←nodes 0 0];exact PolynomialExpression.nodes_pos _
  exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩)
theorem output_bounds (row column : Fin 24) : 500≤output row column ∧ output row column<1076 := by
  unfold output
  omega
theorem output_mem (row column : Fin 24) : output row column∈bank := by
  have h:=output_bounds row column
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_Ico.mpr h))

theorem result_keep (row column : Fin 24) (v : ℕ→Parts) (i : ℕ)
    (hi:i<1200) (different:i≠output row column) : result row column v i=v i := by
  rw [result,Function.update_of_ne different]
  exact control_keep _ _ _ _ hi

theorem executes (row column : Fin 24) (v : ℕ→Parts) (B : ℕ) (positive:1≤B)
    (literals:(expression row column).literalBound≤B) (hw:WidthBank bank B v) (hg:Good bank v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready:Ready bank v s) :
    ∃cost t,Executes input tape (code row column) cost s t ∧ cost≤costBound B ∧
      Ready bank (result row column v) t ∧ Good bank (result row column v) ∧
      WidthBank bank (width B) (result row column v) ∧
      (result row column v (output row column)).value=(expression row column).evaluate (valueBank v) ∧
      BinaryPrecision.Frame (workspace bank) s.val t.val := by
  obtain ⟨c0,u,e0,b0,ready0,good0,width0,value,_,frame0⟩:=
    executes_computed_in bank (expression row column) 1200 B (valid row column)
      (expression_scoped row column) positive (literalsFit_bound _ B literals) v hw hg input tape s ready
  have different:1200≠output row column:=by have h:=output_bounds row column;omega
  obtain ⟨c1,t,e1,b1,ready1,width1,frame1⟩:=
    partsCopy_executes bank 1200 (output row column) scratch_mem (output_mem row column) different
      _ ((expression row column).width B) width0 input tape u ready0
  refine ⟨c0+c1,t,e0.seq e1,?_,ready1,?_,?_,?_,frame0.trans frame1⟩
  · have h:=Nat.add_le_add b0 b1
    simpa only [PolynomialExpression.cost,PolynomialExpression.width,nodes,width,costBound] using h
  · intro i hi
    by_cases eq:i=output row column
    · simpa only [result,eq,Function.update_self] using good0 1200 scratch_mem
    · simpa only [result,Function.update_of_ne eq] using good0 i hi
  · simpa only [PolynomialExpression.width,nodes,width,result] using width1
  · simpa only [result,Function.update_self] using value

#print axioms executes
end Maxwell.Continuum.Calibration.SchurRow
