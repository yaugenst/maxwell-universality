import Maxwell.Continuum.RationalDataflowSubbank

/-! Total reciprocal with an actual zero branch. A zero input produces a
valid denominator-one zero; nonzero inputs use the signed reciprocal code. -/
namespace Maxwell.Continuum.RationalDataflow.TotalInverse
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def control (target source work : ℕ) : Control :=
  .positive source (.step (.inverse target source) .done)
    (.step (.literal work 0) (.step (.binary .sub work work source)
      (.positive work (.step (.inverse target source) .done) (.step (.literal target 0) .done))))

def negated (v : ℕ → Parts) (source work : ℕ) : ℕ → Parts :=
  (Instruction.binary .sub work work source).update ((Instruction.literal work 0).update v)

theorem negated_source (v : ℕ → Parts) (source work : ℕ) (hne : source≠work) :
    negated v source work source=v source := by
  simp [negated,Instruction.update,hne]

theorem negated_value (v : ℕ → Parts) (source work : ℕ) (hne : source≠work)
    (hv : (v source).Valid) : (negated v source work work).value=-(v source).value := by
  simp only [negated,Instruction.update,Function.update_self,Function.update_of_ne hne,BinaryOp.eval]
  rw [Parts.sub_value _ _ (Parts.literal_valid 0) hv,Parts.literal_value,zero_sub]

theorem valid (S : Finset ℕ) (target source work : ℕ)
    (ht : target∈S) (hs : source∈S) (hw : work∈S) : (control target source work).Valid S := by
  simp [control,Control.Valid,Instruction.Valid,ht,hs,hw]

theorem literals (target source work B : ℕ) (hB : 1≤B) :
    (control target source work).LiteralsFit B := by
  have zero := (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
  simpa only [control,Control.LiteralsFit,Instruction.LiteralFits,and_true,true_and,and_self] using zero

theorem steps (target source work : ℕ) : (control target source work).steps=5 := rfl

theorem admissible (target source work : ℕ) (hne : source≠work)
    (v : ℕ → Parts) (hv : (v source).Valid) : (control target source work).AdmissibleTrace v := by
  by_cases hp : 0<(v source).value
  · simp only [control,Control.AdmissibleTrace,hp,ite_true,Instruction.Admissible,and_true]
    exact ne_of_gt hp
  · simp only [control,Control.AdmissibleTrace,hp,ite_false,Instruction.Admissible,true_and,and_true]
    change if 0<(negated v source work work).value then
      (negated v source work source).value≠0 else True
    rw [negated_value v source work hne hv,negated_source v source work hne]
    split_ifs with hn
    · linarith

theorem rational_value (target source work : ℕ) (hne : source≠work)
    (v : ℕ → ℚ) : (control target source work).rationalEvaluate v target=(v source)⁻¹ := by
  by_cases hp : 0<v source
  · simp [control,Control.rationalEvaluate,Instruction.rationalUpdate,hp]
  · simp only [control,Control.rationalEvaluate,hp,ite_false,Instruction.rationalUpdate,
      Function.update_self,Function.update_of_ne hne,zero_sub]
    split_ifs with hn
    · simp only [Function.update_self]
    · have hz : v source=0 := by linarith
      simp only [Function.update_self,hz,inv_zero]

theorem rational_keep (target source work : ℕ) (v : ℕ → ℚ) (i : ℕ)
    (ht : i≠target) (hw : i≠work) : (control target source work).rationalEvaluate v i=v i := by
  simp only [control,Control.rationalEvaluate]
  split_ifs <;> simp_all [Instruction.rationalUpdate]

theorem executes (S : Finset ℕ) (target source work B : ℕ) (hB : 1≤B)
    (ht : target∈S) (hs : source∈S) (hw : work∈S) (hne : source≠work)
    (v : ℕ → Parts) (width : WidthBank S B v) (good : Good S v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (ready : Ready S v s) :
    ∃cost t out,Executes input tape (control target source work).code cost s t ∧
      cost≤5*operationCost (32*(B+1))+1 ∧ Ready S out t ∧ Good S out ∧
      WidthBank S (32*(B+1)) out ∧ (out target).value=(v source).value⁻¹ ∧
      (∀i,i≠target → i≠work → (out i).value=(v i).value) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have valid := valid S target source work ht hs hw
  have admissible := admissible target source work hne v (good source hs)
  have trace := (control target source work).automatic_widthTrace S valid v B width
    (literals target source work B hB)
  rw [steps] at trace
  obtain ⟨c,t,e,hc,b,f⟩ := (control target source work).executes S valid v (32*(B+1)) trace
    good admissible input tape s ready
  rw [steps] at hc
  have values := (control target source work).evaluate_value S valid v good admissible
  refine ⟨c,t,(control target source work).evaluate v,e,hc,b,
    (control target source work).evaluate_good S valid v good admissible,trace.result,?_,?_,f⟩
  · exact (congrFun values target).trans (rational_value target source work hne (valueBank v))
  · intro i hi hi'
    exact (congrFun values i).trans (rational_keep target source work (valueBank v) i hi hi')

#print axioms executes
end Maxwell.Continuum.RationalDataflow.TotalInverse
