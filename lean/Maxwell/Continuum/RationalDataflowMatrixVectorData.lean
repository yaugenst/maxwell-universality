import Maxwell.Continuum.RationalDataflowExpressionVector
import Maxwell.Continuum.RationalDataflowDeterminant

/-! Row-major rational matrix/vector layouts with disjoint output and
scratch regions. All dimensions and addresses are fixed program parameters. -/
namespace Maxwell.Continuum.RationalDataflow.MatrixVector
open PolynomialExpression
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

structure Layout (n : ℕ) where
  matrixBase : ℕ
  vectorBase : ℕ
  outputBase : ℕ
  scratchBase : ℕ
  matrixBelow : matrixBase+n*n≤outputBase
  vectorBelow : vectorBase+n≤outputBase
  outputBelow : outputBase+n≤scratchBase

variable {n : ℕ}

def Layout.matrix (q : Layout n) (i j : Fin n) : ℕ := q.matrixBase+n*i.val+j.val
def Layout.vector (q : Layout n) (j : Fin n) : ℕ := q.vectorBase+j.val
def Layout.output (q : Layout n) (i : Fin n) : ℕ := q.outputBase+i.val
def Layout.expression (q : Layout n) (i : Fin n) : PolynomialExpression :=
  sum (List.ofFn (fun j : Fin n=>.binary .mul (.inputRegister (q.matrix i j)) (.inputRegister (q.vector j))))
def Layout.bank (q : Layout n) : Finset ℕ :=
  ((Finset.Ico q.matrixBase (q.matrixBase+n*n)∪Finset.Ico q.vectorBase (q.vectorBase+n))∪
    Finset.Ico q.outputBase (q.outputBase+n))∪Finset.Ico q.scratchBase (q.scratchBase+4*n+1)

theorem Layout.matrix_range (q : Layout n) (i j : Fin n) :
    q.matrixBase≤q.matrix i j ∧ q.matrix i j<q.matrixBase+n*n := by
  have row : n*(i.val+1)≤n*n := Nat.mul_le_mul_left n i.isLt
  simp only [Nat.mul_add,Nat.mul_one] at row
  unfold Layout.matrix
  omega

theorem Layout.vector_range (q : Layout n) (j : Fin n) :
    q.vectorBase≤q.vector j ∧ q.vector j<q.vectorBase+n := by
  unfold Layout.vector
  omega

theorem Layout.output_range (q : Layout n) (i : Fin n) :
    q.outputBase≤q.output i ∧ q.output i<q.outputBase+n := by
  unfold Layout.output
  omega

theorem Layout.output_injective (q : Layout n) : Function.Injective q.output := by
  intro i j eq
  apply Fin.ext
  unfold Layout.output at eq
  omega

private theorem inputs_sum (xs : List PolynomialExpression) (i : ℕ) :
    i∈(sum xs).inputs ↔ ∃e∈xs,i∈e.inputs := by
  induction xs with
  | nil => simp [sum,inputs]
  | cons e rest ih => simp [sum,inputs,ih]

theorem Layout.input_cases (q : Layout n) (r : Fin n) (i : ℕ) (hi : i∈(q.expression r).inputs) :
    (∃j,i=q.matrix r j) ∨ (∃j,i=q.vector j) := by
  obtain ⟨e,he,member⟩:=(inputs_sum _ i).mp hi
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
  simp only [inputs,Finset.mem_union,Finset.mem_singleton] at member
  exact member.elim (fun h=>Or.inl ⟨j,h⟩) (fun h=>Or.inr ⟨j,h⟩)

theorem Layout.input_below (q : Layout n) (r : Fin n) (i : ℕ) (hi : i∈(q.expression r).inputs) :
    i<q.outputBase := by
  rcases q.input_cases r i hi with ⟨j,rfl⟩|⟨j,rfl⟩
  · exact (q.matrix_range r j).2.trans_le q.matrixBelow
  · exact (q.vector_range j).2.trans_le q.vectorBelow

theorem Layout.expression_scoped (q : Layout n) (r : Fin n) : (q.expression r).Scoped q.scratchBase := by
  apply sum_scoped
  intro e he
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
  exact ⟨((q.matrix_range r j).2.trans_le q.matrixBelow).trans_le (by have := q.outputBelow;omega),
    ((q.vector_range j).2.trans_le q.vectorBelow).trans_le (by have := q.outputBelow;omega)⟩

theorem Layout.expression_nodes (q : Layout n) (r : Fin n) : (q.expression r).nodes≤4*n+1 := by
  have h:=sum_nodes (List.ofFn (fun j : Fin n=>
    .binary .mul (.inputRegister (q.matrix r j)) (.inputRegister (q.vector j)))) 3 (by
      intro e he
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
      rfl)
  simpa only [Layout.expression,List.length_ofFn,Nat.mul_comm] using h

private theorem sum_literalBound (xs : List PolynomialExpression)
    (h : ∀e∈xs,e.literalBound≤1) : (sum xs).literalBound≤1 := by
  induction xs with
  | nil => decide +kernel
  | cons e rest ih =>
    exact max_le (h e (by simp)) (ih (fun a ha=>h a (List.mem_cons_of_mem _ ha)))

theorem Layout.expression_literals (q : Layout n) (r : Fin n) : (q.expression r).literalBound≤1 := by
  apply sum_literalBound
  intro e he
  obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
  change max 0 0≤1
  decide

theorem Layout.expression_value (q : Layout n) (r : Fin n) (v : ℕ→ℚ) :
    (q.expression r).evaluate v=∑j,v (q.matrix r j)*v (q.vector j) := by
  simp only [Layout.expression,sum_evaluate,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    PolynomialExpression.evaluate,binaryValue]

theorem Layout.valid (q : Layout n) (r : Fin n) : ((q.expression r).control q.scratchBase).Valid q.bank := by
  apply Control.prepend_valid
  · apply instructions_valid_in
    · intro i hi
      rcases q.input_cases r i hi with ⟨j,rfl⟩|⟨j,rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_Ico.mpr (q.matrix_range r j))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_Ico.mpr (q.vector_range j))))
    · intro i lo hi
      have := q.expression_nodes r
      exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨lo,by omega⟩)
  · trivial

#print axioms Layout.valid
end Maxwell.Continuum.RationalDataflow.MatrixVector
