import Maxwell.Continuum.RationalDataflowExpression
import Maxwell.Continuum.RationalDataflowTotalInverse

/-! A total rational quotient circuit with proved arithmetic execution and
input-independent syntax. This includes the zero-denominator convention. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem Control.andThen_rational (c next : Control) (v : ℕ → ℚ) :
    (c.andThen next).rationalEvaluate v=next.rationalEvaluate (c.rationalEvaluate v) := by
  induction c generalizing v with
  | done => rfl
  | step a rest ih => exact ih (a.rationalUpdate v)
  | positive source yes no iy ino =>
    simp only [Control.andThen,Control.rationalEvaluate]
    split_ifs <;> simp only [iy,ino]

namespace QuotientExpression
open PolynomialExpression

def multiply (base : ℕ) : Control := .step (.binary .mul base base (base+1)) .done
def control (p q : PolynomialExpression) (base : ℕ) : Control :=
  (p.control base).andThen ((q.control (base+1)).andThen
    ((TotalInverse.control (base+1) (base+1) (base+2)).andThen (multiply base)))
def registers (p q : PolynomialExpression) (base : ℕ) : Finset ℕ :=
  Finset.range (base+p.nodes+q.nodes+3)
def steps (p q : PolynomialExpression) : ℕ := 3*(p.nodes+q.nodes)+6
def width (p q : PolynomialExpression) (B : ℕ) : ℕ := 2^(steps p q)*(B+1)
def cost (p q : PolynomialExpression) (B : ℕ) : ℕ :=
  steps p q*operationCost (width p q B)+1

theorem control_steps (p q : PolynomialExpression) (base : ℕ) :
    (control p q base).steps≤steps p q := by
  have hp := p.instructions_length base
  have hq := q.instructions_length (base+1)
  simp only [control,Control.andThen_steps,PolynomialExpression.control,Control.prepend_steps,
    Control.steps,TotalInverse.steps,multiply,add_zero,steps]
  omega

theorem valid (p q : PolynomialExpression) (base : ℕ) (hp : p.Scoped base) (hq : q.Scoped base) :
    (control p q base).Valid (registers p q base) := by
  have positive := p.nodes_pos
  have v0 := p.control_valid base (base+p.nodes+q.nodes+3) hp (by omega)
  have v1 := q.control_valid (base+1) (base+p.nodes+q.nodes+3) (hq.mono (by omega)) (by omega)
  have v2 := TotalInverse.valid (registers p q base) (base+1) (base+1) (base+2)
    (by simp [registers];omega) (by simp [registers];omega) (by simp [registers];omega)
  exact Control.andThen_valid _ _ _ v0 (Control.andThen_valid _ _ _ v1 (Control.andThen_valid _ _ _ v2 (by
    simp [multiply,Control.Valid,Instruction.Valid,registers]
    omega)))

theorem literals (p q : PolynomialExpression) (base B : ℕ) (hB : 1≤B)
    (hp : p.LiteralsFit B) (hq : q.LiteralsFit B) : (control p q base).LiteralsFit B :=
  Control.andThen_literals _ _ B (p.control_literals base B hB hp)
    (Control.andThen_literals _ _ B (q.control_literals (base+1) B hB hq)
      (Control.andThen_literals _ _ B (TotalInverse.literals _ _ _ B hB) ⟨trivial,trivial⟩))

theorem rational_result (p q : PolynomialExpression) (base : ℕ)
    (hp : p.Scoped base) (hq : q.Scoped base) (v : ℕ → ℚ) :
    (control p q base).rationalEvaluate v base=p.evaluate v*(q.evaluate v)⁻¹ ∧
    ∀i,i<base → (control p q base).rationalEvaluate v i=v i := by
  let u := (p.control base).rationalEvaluate v
  let w := (q.control (base+1)).rationalEvaluate u
  let z := (TotalInverse.control (base+1) (base+1) (base+2)).rationalEvaluate w
  have first : u base=p.evaluate v ∧ ∀i,i<base → u i=v i := by
    simpa only [u,p.control_rational] using p.rational_result base hp v
  have second : w (base+1)=q.evaluate u ∧ ∀i,i<base+1 → w i=u i := by
    simpa only [w,q.control_rational] using q.rational_result (base+1) (hq.mono (by omega)) u
  have numerator : z base=p.evaluate v :=
    (TotalInverse.rational_keep (base+1) (base+1) (base+2) w base (by omega) (by omega)).trans
      ((second.2 base (by omega)).trans first.1)
  have denominator : z (base+1)=(q.evaluate v)⁻¹ := by
    dsimp only [z]
    rw [TotalInverse.rational_value _ _ _ (by omega),second.1,
      q.evaluate_congr base hq u v first.2]
  have same (i : ℕ) (hi : i<base) : z i=v i :=
    (TotalInverse.rational_keep (base+1) (base+1) (base+2) w i (by omega) (by omega)).trans
      ((second.2 i (by omega)).trans (first.2 i hi))
  simp only [control,Control.andThen_rational]
  change (multiply base).rationalEvaluate z base=_ ∧ ∀i,i<base → (multiply base).rationalEvaluate z i=v i
  simp only [multiply,Control.rationalEvaluate,Instruction.rationalUpdate,Function.update_self,
    numerator,denominator]
  refine ⟨trivial,?_⟩
  intro i hi
  rw [Function.update_of_ne (by omega : i≠base)]
  exact same i hi

theorem admissible (p q : PolynomialExpression) (base : ℕ)
    (hp : p.Scoped base) (hq : q.Scoped base) (S : Finset ℕ)
    (hS : registers p q base⊆S) (v : ℕ → Parts) (hg : Good S v) :
    (control p q base).AdmissibleTrace v := by
  have vp := (p.control_valid base (base+p.nodes+q.nodes+3) hp (by omega)).mono hS
  have vq := (q.control_valid (base+1) (base+p.nodes+q.nodes+3) (hq.mono (by omega)) (by
    have := p.nodes_pos
    omega)).mono hS
  have ap := p.control_admissible base v
  have aq := q.control_admissible (base+1) ((p.control base).evaluate v)
  have goodq := (q.control (base+1)).evaluate_good S vq _
    ((p.control base).evaluate_good S vp v hg ap) aq
  have ai := TotalInverse.admissible (base+1) (base+1) (base+2) (by omega) _
    (goodq (base+1) (hS (by simp [registers];omega)))
  exact Control.andThen_admissible _ _ v ap (Control.andThen_admissible _ _ _ aq
    (Control.andThen_admissible _ _ _ ai ⟨trivial,trivial⟩))

theorem executes (p q : PolynomialExpression) (base B : ℕ)
    (hp : p.Scoped base) (hq : q.Scoped base) (hB : 1≤B)
    (hlp : p.LiteralsFit B) (hlq : q.LiteralsFit B) (v : ℕ → Parts)
    (hw : WidthBank (registers p q base) B v) (hg : Good (registers p q base) v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready (registers p q base) v s) :
    ∃steps t out,Executes input tape (control p q base).code steps s t ∧ steps≤cost p q B ∧
      Ready (registers p q base) out t ∧ Good (registers p q base) out ∧
      WidthBank (registers p q base) (width p q B) out ∧
      (out base).value=p.evaluate (valueBank v)*(q.evaluate (valueBank v))⁻¹ ∧
      (∀i,i<base → (out i).value=(v i).value) ∧
      BinaryPrecision.Frame (workspace (registers p q base)) s.val t.val := by
  let S := registers p q base
  have vp := p.control_valid base (base+p.nodes+q.nodes+3) hp (by omega)
  have vq := q.control_valid (base+1) (base+p.nodes+q.nodes+3) (hq.mono (by omega)) (by
    have := p.nodes_pos
    omega)
  have ap := p.control_admissible base v
  have aq := q.control_admissible (base+1) ((p.control base).evaluate v)
  have goodq := (q.control (base+1)).evaluate_good S vq _
    ((p.control base).evaluate_good S vp v hg ap) aq
  have ai := TotalInverse.admissible (base+1) (base+1) (base+2) (by omega) _
    (goodq (base+1) (by simp [S,registers];omega))
  have admissible : (control p q base).AdmissibleTrace v :=
    Control.andThen_admissible _ _ v ap (Control.andThen_admissible _ _ _ aq
      (Control.andThen_admissible _ _ _ ai ⟨trivial,trivial⟩))
  have valid := valid p q base hp hq
  have trace := (control p q base).automatic_widthTrace S valid v B hw
    (literals p q base B hB hlp hlq)
  have trace' := trace.mono (Nat.mul_le_mul_right (B+1)
    (Nat.pow_le_pow_right (by decide) (control_steps p q base)))
  obtain ⟨c,t,e,hc,b,f⟩ := (control p q base).executes S valid v (width p q B) trace'
    hg admissible input tape s hs
  have values := (control p q base).evaluate_value S valid v hg admissible
  have result := rational_result p q base hp hq (valueBank v)
  exact ⟨c,t,(control p q base).evaluate v,e,
    hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (control_steps p q base)) 1),b,
    (control p q base).evaluate_good S valid v hg admissible,trace'.result,
    (congrFun values base).trans result.1,
    fun i hi => (congrFun values i).trans (result.2 i hi),f⟩

#print axioms executes
end QuotientExpression
end Maxwell.Continuum.RationalDataflow
