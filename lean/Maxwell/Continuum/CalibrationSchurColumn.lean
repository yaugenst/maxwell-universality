import Maxwell.Continuum.CalibrationSchurRow

/-! The fixed 24-row circuit fills one central Schur column. Literal widths
are a single input-independent constant; every intermediate width and cost
is obtained from the executed arithmetic. -/
namespace Maxwell.Continuum.Calibration.SchurColumn
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PolynomialExpression
open SchurRow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def literalBudget : ℕ := max 1 ((Finset.univ : Finset (Fin 24×Fin 24)).sup
  (fun p=>(SchurExpression.expression p.1 p.2).literalBound))
theorem literal_fits (row column : Fin 24) : (SchurExpression.expression row column).literalBound≤literalBudget :=
  (Finset.le_sup (s := (Finset.univ : Finset (Fin 24×Fin 24)))
    (f := fun p : Fin 24×Fin 24=>(SchurExpression.expression p.1 p.2).literalBound)
    (Finset.mem_univ (row,column))).trans (le_max_right _ _)
theorem literal_positive : 1≤literalBudget := le_max_left _ _

def code (column : Fin 24) : List (Fin 24)→Code
  | [] => .skip
  | row::rest => .seq (SchurRow.code row column) (code column rest)
def values (column : Fin 24) : List (Fin 24)→(ℕ→Parts)→(ℕ→Parts)
  | [],v => v
  | row::rest,v => values column rest (SchurRow.result row column v)
def resultWidth : List (Fin 24)→ℕ→ℕ
  | [],B => B
  | _::rest,B => resultWidth rest (SchurRow.width B)
def costBound : List (Fin 24)→ℕ→ℕ
  | [],_ => 1
  | _::rest,B => SchurRow.costBound B+costBound rest (SchurRow.width B)

attribute [local irreducible] literalBudget SchurRow.nodeCount

theorem width_ge (B : ℕ) : B≤SchurRow.width B := by
  have h:=Nat.mul_le_mul_right (B+1) (Nat.one_le_pow (3*SchurRow.nodeCount) 2 (by decide))
  unfold SchurRow.width
  omega

theorem values_keep (column : Fin 24) (rows : List (Fin 24)) (v : ℕ→Parts) (i : ℕ)
    (lo:i<1200) (unused:∀r∈rows,i≠SchurRow.output r column) : values column rows v i=v i := by
  induction rows generalizing v with
  | nil => rfl
  | cons row rest ih =>
    rw [values,ih _ (fun r hr=>unused r (by simp [hr]))]
    exact SchurRow.result_keep row column v i lo (unused row (by simp))

theorem expression_keep (row source column : Fin 24) (v : ℕ→Parts) :
    (SchurExpression.expression row column).evaluate (valueBank (SchurRow.result source column v))=
      (SchurExpression.expression row column).evaluate (valueBank v) := by
  apply evaluate_inputs_congr
  intro i hi
  have bound:=SchurRow.input_bounds row column i hi
  have outputBound:=SchurRow.output_bounds source column
  unfold valueBank
  rw [SchurRow.result_keep source column v i (by omega) (by omega)]

theorem output_injective (column r q : Fin 24) (eq:SchurRow.output r column=SchurRow.output q column) : r=q := by
  apply Fin.ext
  simp only [SchurRow.output] at eq
  omega

theorem executes (column : Fin 24) (rows : List (Fin 24)) (v : ℕ→Parts) (B : ℕ)
    (large:literalBudget≤B) (hw:WidthBank bank B v) (hg:Good bank v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready:Ready bank v s) :
    ∃cost t,Executes input tape (code column rows) cost s t ∧ cost≤costBound rows B ∧
      Ready bank (values column rows v) t ∧ Good bank (values column rows v) ∧
      WidthBank bank (resultWidth rows B) (values column rows v) ∧
      (∀row∈rows,(values column rows v (SchurRow.output row column)).value=
        (SchurExpression.expression row column).evaluate (valueBank v)) ∧
      BinaryPrecision.Frame (workspace bank) s.val t.val := by
  induction rows generalizing v B s with
  | nil => exact ⟨1,s,.skip s,le_rfl,ready,hg,hw,by simp,BinaryPrecision.Frame.refl _ _⟩
  | cons row rest ih =>
    obtain ⟨c0,u,e0,b0,ready0,good0,width0,value0,frame0⟩:=
      SchurRow.executes row column v B (literal_positive.trans large)
        ((literal_fits row column).trans large) hw hg input tape s ready
    obtain ⟨c1,t,e1,b1,ready1,good1,width1,value1,frame1⟩:=
      ih _ (SchurRow.width B) (large.trans (width_ge B)) width0 good0 u ready0
    refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add b0 b1,ready1,good1,width1,?_,frame0.trans frame1⟩
    intro r hr
    rcases List.mem_cons.mp hr with eq|hr
    · subst r
      by_cases tail:row∈rest
      · exact (value1 row tail).trans (expression_keep row row column v)
      · rw [values,values_keep column rest _ _ (lt_trans (output_bounds row column).2 (by decide : 1076<1200))]
        · exact value0
        · intro q hq eq
          exact tail ((output_injective column row q eq).symm ▸ hq)
    · exact (value1 r hr).trans (expression_keep r row column v)

#print axioms executes
end Maxwell.Continuum.Calibration.SchurColumn
