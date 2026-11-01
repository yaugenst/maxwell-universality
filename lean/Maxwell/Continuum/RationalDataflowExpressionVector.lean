import Maxwell.Continuum.RationalDataflowExpressionRegisters
import Maxwell.Continuum.RationalDataflowExpressionFrame
import Maxwell.Continuum.RationalDataflowExpressionBounds
import Maxwell.Continuum.RationalDataflowPartsCopy

/-! A fixed family of expressions shares one scratch range and writes
distinct output cells. The compiler, loop proof, and charged bounds do not
depend on the matrix or physical model represented by those expressions. -/
namespace Maxwell.Continuum.RationalDataflow.ExpressionVector
open Maxwell.Cost Maxwell.Cost.Structured PolynomialExpression
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

variable {n : ℕ}

def rowResult (e : PolynomialExpression) (base target : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  let computed:=(e.control base).evaluate v
  Function.update computed target (computed base)
def rowCode (e : PolynomialExpression) (base target : ℕ) : Code :=
  .seq (e.control base).code (partsCopyCode base target)
def rowCost (e : PolynomialExpression) (B : ℕ) : ℕ := e.cost B+stageCost (e.width B)

theorem row_keep (e : PolynomialExpression) (base target : ℕ) (v : ℕ→Parts) (i : ℕ)
    (lo : i<base) (different : i≠target) : rowResult e base target v i=v i := by
  rw [rowResult,Function.update_of_ne different,control_keep e base v i lo]

theorem row_executes (S : Finset ℕ) (e : PolynomialExpression) (base target B : ℕ)
    (valid : (e.control base).Valid S) (scope : e.Scoped base)
    (baseMem : base∈S) (targetMem : target∈S) (targetBelow : target<base)
    (positive : 1≤B) (literals : e.LiteralsFit B) (v : ℕ→Parts)
    (width : WidthBank S B v) (good : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready S v s) :
    ∃steps t,Executes input tape (rowCode e base target) steps s t ∧ steps≤rowCost e B ∧
      Ready S (rowResult e base target v) t ∧ Good S (rowResult e base target v) ∧
      WidthBank S (e.width B) (rowResult e base target v) ∧
      (rowResult e base target v target).value=e.evaluate (valueBank v) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c,a,ex,charge,stored,validParts,bounded,value,_,frame⟩:=
    executes_computed_in S e base B valid scope positive literals v width good input tape s ready
  obtain ⟨d,t,et,dt,output,wt,ft⟩:=partsCopy_executes S base target baseMem targetMem (by omega)
    _ (e.width B) bounded input tape a stored
  refine ⟨c+d,t,ex.seq et,Nat.add_le_add charge dt,output,?_,wt,?_,frame.trans ft⟩
  · intro i hi
    by_cases same : i=target
    · simpa only [rowResult,same,Function.update_self] using validParts base baseMem
    · simpa only [rowResult,Function.update_of_ne same] using validParts i hi
  · simpa only [rowResult,Function.update_self] using value

def code (e : Fin n→PolynomialExpression) (base : ℕ) (output : Fin n→ℕ) : List (Fin n)→Code
  | [] => .skip
  | row::rest => .seq (rowCode (e row) base (output row)) (code e base output rest)
def values (e : Fin n→PolynomialExpression) (base : ℕ) (output : Fin n→ℕ) :
    List (Fin n)→(ℕ→Parts)→(ℕ→Parts)
  | [],v => v
  | row::rest,v => values e base output rest (rowResult (e row) base (output row) v)
def resultWidth (e : Fin n→PolynomialExpression) : List (Fin n)→ℕ→ℕ
  | [],B => B
  | row::rest,B => resultWidth e rest ((e row).width B)
def cost (e : Fin n→PolynomialExpression) : List (Fin n)→ℕ→ℕ
  | [],_ => 1
  | row::rest,B => rowCost (e row) B+cost e rest ((e row).width B)

theorem width_ge (e : PolynomialExpression) (B : ℕ) : B≤e.width B := by
  have h:=Nat.mul_le_mul_right (B+1) (Nat.one_le_pow (3*e.nodes) 2 (by decide))
  unfold PolynomialExpression.width
  omega

theorem values_keep (e : Fin n→PolynomialExpression) (base : ℕ) (output : Fin n→ℕ)
    (rows : List (Fin n)) (v : ℕ→Parts) (i : ℕ) (below : i<base)
    (unused : ∀r∈rows,i≠output r) : values e base output rows v i=v i := by
  induction rows generalizing v with
  | nil => rfl
  | cons r rest ih =>
    rw [values,ih _ (fun q hq=>unused q (List.mem_cons_of_mem _ hq)),
      row_keep (e r) base (output r) v i below (unused r (by simp))]

theorem executes (S : Finset ℕ) (e : Fin n→PolynomialExpression) (base : ℕ)
    (output : Fin n→ℕ) (injective : Function.Injective output)
    (valid : ∀r,((e r).control base).Valid S) (scope : ∀r,(e r).Scoped base)
    (baseMem : base∈S) (outputMem : ∀r,output r∈S) (below : ∀r,output r<base)
    (inputBelow : ∀r,∀i∈(e r).inputs,i<base)
    (separated : ∀r q,∀i∈(e r).inputs,i≠output q)
    (L : ℕ) (positive : 1≤L) (literals : ∀r,(e r).literalBound≤L)
    (rows : List (Fin n)) (v : ℕ→Parts) (B : ℕ) (large : L≤B)
    (width : WidthBank S B v) (good : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready S v s) :
    ∃steps t,Executes input tape (code e base output rows) steps s t ∧ steps≤cost e rows B ∧
      Ready S (values e base output rows v) t ∧ Good S (values e base output rows v) ∧
      WidthBank S (resultWidth e rows B) (values e base output rows v) ∧
      (∀r∈rows,(values e base output rows v (output r)).value=(e r).evaluate (valueBank v)) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have preserved (r q : Fin n) (v : ℕ→Parts) :
      (e r).evaluate (valueBank (rowResult (e q) base (output q) v))=(e r).evaluate (valueBank v) := by
    apply evaluate_inputs_congr
    intro i hi
    unfold valueBank
    rw [row_keep (e q) base (output q) v i (inputBelow r i hi) (separated r q i hi)]
  induction rows generalizing v B s with
  | nil => exact ⟨1,s,.skip s,le_rfl,ready,good,width,by simp,BinaryPrecision.Frame.refl _ _⟩
  | cons r rest ih =>
    obtain ⟨c,a,ex,charge,stored,validParts,bounded,value,frame⟩:=row_executes S (e r) base (output r) B
      (valid r) (scope r) baseMem (outputMem r) (below r) (positive.trans large)
      (literalsFit_bound (e r) B ((literals r).trans large)) v width good input tape s ready
    obtain ⟨d,t,et,dt,outputReady,outputGood,outputWidth,outputValues,ft⟩:=
      ih _ ((e r).width B) (large.trans (width_ge (e r) B)) bounded validParts a stored
    refine ⟨c+d,t,ex.seq et,Nat.add_le_add charge dt,outputReady,outputGood,outputWidth,?_,frame.trans ft⟩
    intro q hq
    rcases List.mem_cons.mp hq with same|tail
    · subst q
      by_cases member : r∈rest
      · exact (outputValues r member).trans (preserved r r v)
      · rw [values,values_keep e base output rest _ (output r) (below r)]
        · exact value
        · intro q hq eq
          exact member ((injective eq).symm ▸ hq)
    · exact (outputValues q tail).trans (preserved q r v)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.ExpressionVector
