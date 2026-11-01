import Maxwell.Continuum.RationalDataflowMatrixVectorData

/-! Fixed rational matrix/vector code with actual stored output cells,
representation preservation, and charged finite resource bounds. -/
namespace Maxwell.Continuum.RationalDataflow.MatrixVector
open Maxwell.Cost Maxwell.Cost.Structured PolynomialExpression
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

variable {n : ℕ}
def Layout.code (q : Layout n) : Code := ExpressionVector.code q.expression q.scratchBase q.output (List.finRange n)
def Layout.values (q : Layout n) (v : ℕ→Parts) : ℕ→Parts :=
  ExpressionVector.values q.expression q.scratchBase q.output (List.finRange n) v
def Layout.cost (q : Layout n) (B : ℕ) : ℕ := ExpressionVector.cost q.expression (List.finRange n) B
def Layout.width (q : Layout n) (B : ℕ) : ℕ := ExpressionVector.resultWidth q.expression (List.finRange n) B

theorem Layout.executes (q : Layout n) (v : ℕ→Parts) (B : ℕ) (positive : 1≤B)
    (width : WidthBank q.bank B v) (good : Good q.bank v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready q.bank v s) :
    ∃steps t,Executes input tape q.code steps s t ∧ steps≤q.cost B ∧
      Ready q.bank (q.values v) t ∧ Good q.bank (q.values v) ∧ WidthBank q.bank (q.width B) (q.values v) ∧
      (∀r,(q.values v (q.output r)).value=∑j,(v (q.matrix r j)).value*(v (q.vector j)).value) ∧
      BinaryPrecision.Frame (workspace q.bank) s.val t.val := by
  obtain ⟨c,t,e,charge,stored,validParts,bounded,values,frame⟩:=
    ExpressionVector.executes q.bank q.expression q.scratchBase q.output q.output_injective
      q.valid q.expression_scoped (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl,by omega⟩))
      (fun r=>Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_Ico.mpr (q.output_range r))))
      (fun r=>(q.output_range r).2.trans_le q.outputBelow)
      (fun r i hi=>(q.input_below r i hi).trans_le (by have := q.outputBelow;omega))
      (by intro r j i hi;have := q.input_below r i hi;have := (q.output_range j).1;omega)
      1 (by decide) q.expression_literals (List.finRange n) v B positive width good input tape s ready
  refine ⟨c,t,e,charge,stored,validParts,bounded,?_,frame⟩
  intro r
  simpa only [Layout.values,Layout.expression_value,valueBank] using values r (List.mem_finRange r)

theorem Layout.values_keep (q : Layout n) (v : ℕ→Parts) (i : ℕ) (below : i<q.outputBase) :
    q.values v i=v i := by
  apply ExpressionVector.values_keep
  · have := q.outputBelow
    omega
  · intro r _
    have := (q.output_range r).1
    omega

#print axioms Layout.executes
end Maxwell.Continuum.RationalDataflow.MatrixVector
