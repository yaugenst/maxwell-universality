import Maxwell.Continuum.RationalDataflowControlTraceResult

/-! A reusable compiler for fixed rational polynomial expressions. Scratch
registers start above all inputs; correctness and resource bounds are proved
without expanding a particular expression tree. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

inductive PolynomialExpression where
  | literal (value : ℚ)
  | inputRegister (register : ℕ)
  | binary (op : BinaryOp) (left right : PolynomialExpression)

namespace PolynomialExpression

private theorem rationalEvaluate_append (xs ys : List Instruction) (v : ℕ → ℚ) :
    rationalEvaluate (xs++ys) v=rationalEvaluate ys (rationalEvaluate xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons a xs ih => exact ih (a.rationalUpdate v)

def binaryValue : BinaryOp → ℚ → ℚ → ℚ
  | .add,x,y => x+y
  | .sub,x,y => x-y
  | .mul,x,y => x*y

def evaluate : PolynomialExpression → (ℕ → ℚ) → ℚ
  | .literal q,_ => q
  | .inputRegister i,v => v i
  | .binary op x y,v => binaryValue op (x.evaluate v) (y.evaluate v)

def nodes : PolynomialExpression → ℕ
  | .literal _ => 1
  | .inputRegister _ => 1
  | .binary _ x y => 1+x.nodes+y.nodes

def Scoped (base : ℕ) : PolynomialExpression → Prop
  | .literal _ => True
  | .inputRegister i => i<base
  | .binary _ x y => x.Scoped base ∧ y.Scoped base

def LiteralsFit (B : ℕ) : PolynomialExpression → Prop
  | .literal q => (Parts.literal q).Width B
  | .inputRegister _ => True
  | .binary _ x y => x.LiteralsFit B ∧ y.LiteralsFit B

def instructions : PolynomialExpression → ℕ → List Instruction
  | .literal q,base => [.literal base q]
  | .inputRegister i,base => [.literal base 0,.binary .add base base i]
  | .binary op x y,base =>
      x.instructions base++y.instructions (base+1)++[.binary op base base (base+1)]

def control (e : PolynomialExpression) (base : ℕ) : Control :=
  Control.prepend (e.instructions base) .done
def width (e : PolynomialExpression) (B : ℕ) : ℕ := 2^(3*e.nodes)*(B+1)
def cost (e : PolynomialExpression) (B : ℕ) : ℕ := 3*e.nodes*operationCost (e.width B)+1

theorem nodes_pos (e : PolynomialExpression) : 0<e.nodes := by cases e <;> simp [nodes]

theorem Scoped.mono {e : PolynomialExpression} {a b : ℕ} (h : e.Scoped a) (hab : a≤b) :
    e.Scoped b := by
  induction e with
  | literal => trivial
  | inputRegister i => exact lt_of_lt_of_le h hab
  | binary op x y hx hy => exact ⟨hx h.1,hy h.2⟩

theorem evaluate_congr (e : PolynomialExpression) (base : ℕ) (h : e.Scoped base)
    (v w : ℕ → ℚ) (same : ∀i,i<base → v i=w i) : e.evaluate v=e.evaluate w := by
  induction e with
  | literal => rfl
  | inputRegister i => exact same i h
  | binary op x y hx hy => exact congrArg₂ (binaryValue op) (hx h.1) (hy h.2)

theorem instructions_length (e : PolynomialExpression) (base : ℕ) :
    (e.instructions base).length≤3*e.nodes := by
  induction e generalizing base with
  | literal => simp [instructions,nodes]
  | inputRegister => simp [instructions,nodes]
  | binary op x y hx hy =>
    simp only [instructions,List.length_append,List.length_singleton,nodes]
    have lx := hx base
    have ly := hy (base+1)
    omega

theorem instructions_valid (e : PolynomialExpression) (base limit : ℕ)
    (hscope : e.Scoped base) (space : base+e.nodes≤limit) :
    ∀a∈e.instructions base,a.Valid (Finset.range limit) := by
  induction e generalizing base with
  | literal q =>
    simp only [instructions,List.mem_singleton,forall_eq,Instruction.Valid,Finset.mem_range]
    simp only [nodes] at space
    omega
  | inputRegister i =>
    simp [instructions,Instruction.Valid]
    change i<base at hscope
    simp only [nodes] at space
    omega
  | binary op x y hx hy =>
    have nx := x.nodes_pos
    have ny := y.nodes_pos
    simp only [nodes] at space
    have vx := hx base hscope.1 (by omega)
    have vy := hy (base+1) (hscope.2.mono (by omega)) (by omega)
    intro a ha
    simp only [instructions,List.mem_append,List.mem_singleton] at ha
    rcases ha with (ha|ha)|rfl
    · exact vx a ha
    · exact vy a ha
    · simp only [Instruction.Valid,Finset.mem_range]
      omega

theorem rational_result (e : PolynomialExpression) (base : ℕ) (hscope : e.Scoped base)
    (v : ℕ → ℚ) :
    rationalEvaluate (e.instructions base) v base=e.evaluate v ∧
    ∀i,i<base → rationalEvaluate (e.instructions base) v i=v i := by
  induction e generalizing base v with
  | literal q =>
    simp only [instructions,rationalEvaluate,Instruction.rationalUpdate,evaluate,Function.update_self]
    exact ⟨trivial,fun i hi => Function.update_of_ne (by omega) _ _⟩
  | inputRegister i =>
    have h : i≠base := Nat.ne_of_lt hscope
    simp only [instructions,rationalEvaluate,Instruction.rationalUpdate,evaluate,
      Function.update_self,Function.update_of_ne h,zero_add]
    refine ⟨trivial,?_⟩
    intro j hj
    simp only [Function.update_of_ne (by omega : j≠base)]
  | binary op x y hx hy =>
    let left := rationalEvaluate (x.instructions base) v
    let right := rationalEvaluate (y.instructions (base+1)) left
    have lx := hx base hscope.1 v
    have ry := hy (base+1) (hscope.2.mono (by omega)) left
    have valuey : y.evaluate left=y.evaluate v := y.evaluate_congr base hscope.2 left v lx.2
    have keepx : right base=left base := ry.2 base (by omega)
    have lvalue : left base=x.evaluate v := lx.1
    have rvalue : right (base+1)=y.evaluate v := ry.1.trans valuey
    have keep (i : ℕ) (hi : i<base) : right i=v i :=
      (ry.2 i (by omega)).trans (lx.2 i hi)
    simp only [instructions,rationalEvaluate_append,rationalEvaluate]
    cases op <;>
      simp only [Instruction.rationalUpdate,Function.update_self,evaluate,binaryValue,
        show rationalEvaluate (y.instructions (base+1))
          (rationalEvaluate (x.instructions base) v)=right from rfl,keepx,lvalue,rvalue]
    all_goals
      refine ⟨trivial,?_⟩
      intro i hi
      rw [Function.update_of_ne (by omega : i≠base)]
      exact keep i hi

theorem instructions_literals (e : PolynomialExpression) (base B : ℕ)
    (hB : 1≤B) (hl : e.LiteralsFit B) : ∀a∈e.instructions base,a.LiteralFits B := by
  induction e generalizing base with
  | literal q => simpa only [instructions,List.mem_singleton,forall_eq,Instruction.LiteralFits,LiteralsFit] using hl
  | inputRegister i =>
    simp [instructions,Instruction.LiteralFits]
    exact (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
  | binary op x y hx hy =>
    intro a ha
    simp only [instructions,List.mem_append,List.mem_singleton] at ha
    rcases ha with (ha|ha)|rfl
    · exact hx base hl.1 a ha
    · exact hy (base+1) hl.2 a ha
    · trivial

theorem instructions_admissible (e : PolynomialExpression) (base : ℕ) :
    ∀a∈e.instructions base,∀v,a.Admissible v := by
  induction e generalizing base with
  | literal q => simp [instructions,Instruction.Admissible]
  | inputRegister i => simp [instructions,Instruction.Admissible]
  | binary op x y hx hy =>
    intro a ha v
    simp only [instructions,List.mem_append,List.mem_singleton] at ha
    rcases ha with (ha|ha)|rfl
    · exact hx base a ha v
    · exact hy (base+1) a ha v
    · trivial

private theorem prepend_literals (ins : List Instruction) (B : ℕ)
    (hl : ∀a∈ins,a.LiteralFits B) : (Control.prepend ins .done).LiteralsFit B := by
  induction ins with
  | nil => trivial
  | cons a rest ih => exact ⟨hl a (by simp),ih (fun b hb => hl b (by simp [hb]))⟩

private theorem prepend_admissible (ins : List Instruction)
    (ha : ∀a∈ins,∀v,a.Admissible v) (v : ℕ → Parts) :
    (Control.prepend ins .done).AdmissibleTrace v := by
  induction ins generalizing v with
  | nil => trivial
  | cons a rest ih => exact ⟨ha a (by simp) v,ih (fun b hb => ha b (by simp [hb])) (a.update v)⟩

theorem control_admissible (e : PolynomialExpression) (base : ℕ) (v : ℕ → Parts) :
    (e.control base).AdmissibleTrace v :=
  prepend_admissible (e.instructions base) (e.instructions_admissible base) v

theorem control_literals (e : PolynomialExpression) (base B : ℕ) (hB : 1≤B)
    (hl : e.LiteralsFit B) : (e.control base).LiteralsFit B :=
  prepend_literals (e.instructions base) B (e.instructions_literals base B hB hl)

theorem control_valid (e : PolynomialExpression) (base limit : ℕ) (hscope : e.Scoped base)
    (hlimit : base+e.nodes≤limit) : (e.control base).Valid (Finset.range limit) :=
  Control.prepend_valid _ _ _ (e.instructions_valid base limit hscope hlimit) trivial

theorem control_rational (e : PolynomialExpression) (base : ℕ) (v : ℕ → ℚ) :
    (e.control base).rationalEvaluate v=rationalEvaluate (e.instructions base) v := by
  unfold control
  generalize e.instructions base=ins
  induction ins generalizing v with
  | nil => rfl
  | cons a rest ih => exact ih (a.rationalUpdate v)

theorem executes_computed_in (S : Finset ℕ) (e : PolynomialExpression) (base B : ℕ)
    (valid : (e.control base).Valid S) (hscope : e.Scoped base)
    (hB : 1≤B) (hl : e.LiteralsFit B) (v : ℕ → Parts)
    (hw : WidthBank S B v)
    (hg : Good S v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Ready S v s) :
    let output:=(e.control base).evaluate v
    ∃steps t,Executes input tape (e.control base).code steps s t ∧ steps≤e.cost B ∧
      Ready S output t ∧
      Good S output ∧
      WidthBank S (e.width B) output ∧
      (output base).value=e.evaluate (valueBank v) ∧
      (∀i,i<base → (output i).value=(v i).value) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  dsimp only
  have admissible := prepend_admissible (e.instructions base) (e.instructions_admissible base) v
  have trace := (e.control base).automatic_widthTrace S valid v B hw
    (prepend_literals (e.instructions base) B (e.instructions_literals base B hB hl))
  have steps : (e.control base).steps≤3*e.nodes := by
    simpa only [control,Control.prepend_steps,Control.steps,add_zero] using e.instructions_length base
  have bound : 2^(e.control base).steps*(B+1)≤e.width B :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) steps)
  have trace' := trace.mono bound
  obtain ⟨c,t,run,hc,ready,frame⟩ := (e.control base).executes S valid v (e.width B) trace'
    hg admissible input tape s hs
  have values := (e.control base).evaluate_value S valid v hg admissible
  rw [e.control_rational] at values
  have result := e.rational_result base hscope (valueBank v)
  refine ⟨c,t,run,
    hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ steps) 1),ready,
    (e.control base).evaluate_good S valid v hg admissible,trace'.result,?_,?_,frame⟩
  · exact (congrFun values base).trans result.1
  · intro i hi
    exact (congrFun values i).trans (result.2 i hi)

theorem executes_in (S : Finset ℕ) (e : PolynomialExpression) (base B : ℕ)
    (valid : (e.control base).Valid S) (hscope : e.Scoped base)
    (hB : 1≤B) (hl : e.LiteralsFit B) (v : ℕ → Parts)
    (hw : WidthBank S B v)
    (hg : Good S v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Ready S v s) :
    ∃steps t output,Executes input tape (e.control base).code steps s t ∧ steps≤e.cost B ∧
      Ready S output t ∧
      Good S output ∧
      WidthBank S (e.width B) output ∧
      (output base).value=e.evaluate (valueBank v) ∧
      (∀i,i<base → (output i).value=(v i).value) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,run,bound,ready,good,width,value,keep,frame⟩:=
    executes_computed_in S e base B valid hscope hB hl v hw hg input tape s hs
  exact ⟨cost,t,(e.control base).evaluate v,run,bound,ready,good,width,value,keep,frame⟩

theorem executes (e : PolynomialExpression) (base B : ℕ) (hscope : e.Scoped base)
    (hB : 1≤B) (hl : e.LiteralsFit B) (v : ℕ → Parts)
    (hw : WidthBank (Finset.range (base+e.nodes)) B v)
    (hg : Good (Finset.range (base+e.nodes)) v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Ready (Finset.range (base+e.nodes)) v s) :
    ∃steps t output,Executes input tape (e.control base).code steps s t ∧ steps≤e.cost B ∧
      Ready (Finset.range (base+e.nodes)) output t ∧
      Good (Finset.range (base+e.nodes)) output ∧
      WidthBank (Finset.range (base+e.nodes)) (e.width B) output ∧
      (output base).value=e.evaluate (valueBank v) ∧
      (∀i,i<base → (output i).value=(v i).value) ∧
      BinaryPrecision.Frame (workspace (Finset.range (base+e.nodes))) s.val t.val := by
  exact executes_in (Finset.range (base+e.nodes)) e base B
    (e.control_valid base (base+e.nodes) hscope le_rfl) hscope hB hl v hw hg input tape s hs

#print axioms rational_result
#print axioms executes
end PolynomialExpression
end Maxwell.Continuum.RationalDataflow
