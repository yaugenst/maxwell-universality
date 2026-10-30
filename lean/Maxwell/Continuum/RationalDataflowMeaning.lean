import Maxwell.Continuum.RationalDataflowProgram

/-! The compiled shared-register evaluator implements literal rational arithmetic. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000

def valueBank (v : ℕ→Parts) : ℕ→ℚ := fun i => (v i).value

def Instruction.rationalUpdate : Instruction → (ℕ→ℚ) → (ℕ→ℚ)
  | .literal target q,v => Function.update v target q
  | .binary .add target left right,v => Function.update v target (v left+v right)
  | .binary .sub target left right,v => Function.update v target (v left-v right)
  | .binary .mul target left right,v => Function.update v target (v left*v right)
  | .inverse target source,v => Function.update v target (v source)⁻¹

def rationalEvaluate : List Instruction → (ℕ→ℚ) → (ℕ→ℚ)
  | [],v => v
  | a::rest,v => rationalEvaluate rest (a.rationalUpdate v)

theorem valueBank_update (v : ℕ→Parts) (target : ℕ) (x : Parts) :
    valueBank (Function.update v target x)=Function.update (valueBank v) target x.value := by
  ext i
  by_cases he : i=target
  · subst i; simp [valueBank]
  · simp [valueBank,he]

theorem Instruction.update_value (S : Finset ℕ) (a : Instruction) (ha : a.Valid S)
    (v : ℕ→Parts) (hv : Good S v) (had : a.Admissible v) :
    valueBank (a.update v)=a.rationalUpdate (valueBank v) := by
  cases a with
  | literal target q =>
    exact (valueBank_update v target _).trans (by rw [Parts.literal_value]; rfl)
  | binary op target left right =>
    have hx := hv left ha.2.1
    have hy := hv right ha.2.2
    cases op
    · exact (valueBank_update v target _).trans (by rw [BinaryOp.eval,Parts.add_value _ _ hx hy]; rfl)
    · exact (valueBank_update v target _).trans (by rw [BinaryOp.eval,Parts.sub_value _ _ hx hy]; rfl)
    · exact (valueBank_update v target _).trans (by rw [BinaryOp.eval,Parts.mul_value]; rfl)
  | inverse target source =>
    exact (valueBank_update v target _).trans (by rw [Parts.inverse_value _ (hv source ha.2) had]; rfl)

theorem evaluate_value (S : Finset ℕ) (ins : List Instruction) (hv : ∀ a∈ins, a.Valid S)
    (v : ℕ→Parts) (hg : Good S v) (had : AdmissibleTrace ins v) :
    valueBank (evaluate ins v)=rationalEvaluate ins (valueBank v) := by
  induction ins generalizing v with
  | nil => rfl
  | cons a rest ih =>
    change valueBank (evaluate rest (a.update v))=rationalEvaluate rest (a.rationalUpdate (valueBank v))
    rw [ih (fun b hb => hv b (by simp [hb])) (a.update v)
      (a.update_good S (hv a (by simp)) v hg had.1) had.2]
    rw [a.update_value S (hv a (by simp)) v hg had.1]

theorem rational_program_computes (S : Finset ℕ) (ins : List Instruction) (hv : ∀ a∈ins, a.Valid S)
    (v : ℕ→Parts) (B : ℕ) (hw : WidthTrace S B ins v) (hg : Good S v)
    (had : AdmissibleTrace ins v) (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t output,
      (runPriced ((program ins).compile.next input tape) (ins.length*operationCost B+2) s.val).finished=
        some (t.place (program ins).size) ∧
      (runPriced ((program ins).compile.next input tape) (ins.length*operationCost B+2) s.val).instructions=cost ∧
      cost ≤ ins.length*operationCost B+1 ∧ Ready S output t ∧ Good S output ∧
      valueBank output=rationalEvaluate ins (valueBank v) := by
  obtain ⟨cost,t,hrun,hcost,hc,hb⟩ := program_computes S ins hv v B hw input tape s hs
  exact ⟨cost,t,evaluate ins v,hrun,hcost,hc,hb,evaluate_good S ins hv v hg had,
    evaluate_value S ins hv v hg had⟩

theorem evaluate_append (xs ys : List Instruction) (v : ℕ→Parts) :
    evaluate (xs++ys) v=evaluate ys (evaluate xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons a xs ih => exact ih (a.update v)

theorem widthTrace_append (S : Finset ℕ) (B : ℕ) (xs ys : List Instruction) (v : ℕ→Parts) :
    WidthTrace S B (xs++ys) v ↔ WidthTrace S B xs v ∧ WidthTrace S B ys (evaluate xs v) := by
  induction xs generalizing v with
  | nil =>
    have hfirst : WidthTrace S B ys v → WidthBank S B v := by
      cases ys <;> intro h
      · exact h
      · exact h.1
    exact ⟨fun h => ⟨hfirst h,h⟩,fun h => h.2⟩
  | cons a xs ih =>
    simp only [List.cons_append,WidthTrace,evaluate,ih]
    tauto

#print axioms rational_program_computes

end Maxwell.Continuum.RationalDataflow
