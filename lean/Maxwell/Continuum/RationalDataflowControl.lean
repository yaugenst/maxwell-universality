import Maxwell.Continuum.RationalDataflowMeaning
import Maxwell.Continuum.RationalDataflowPositiveStages

/-! Finite rational control flow with an actual runtime positivity branch. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

inductive Control where
  | done
  | step (instruction : Instruction) (rest : Control)
  | positive (source : ℕ) (yes no : Control)
  deriving DecidableEq, Repr

def Control.steps : Control → ℕ
  | .done => 0
  | .step _ rest => 1+rest.steps
  | .positive _ yes no => 1+max yes.steps no.steps

def Control.code : Control → Code
  | .done => .skip
  | .step a rest => .seq a.code rest.code
  | .positive source yes no => .seq (positivePrefix source)
      (.branch 23 (.seq (NatAssign.code clearMagnitude) yes.code)
        (.seq (NatAssign.code clearMagnitude) no.code))

def Control.evaluate : Control → (ℕ→Parts) → (ℕ→Parts)
  | .done,v => v
  | .step a rest,v => rest.evaluate (a.update v)
  | .positive source yes no,v => if 0<(v source).value then yes.evaluate v else no.evaluate v

def Control.rationalEvaluate : Control → (ℕ→ℚ) → (ℕ→ℚ)
  | .done,v => v
  | .step a rest,v => rest.rationalEvaluate (a.rationalUpdate v)
  | .positive source yes no,v => if 0<v source then yes.rationalEvaluate v else no.rationalEvaluate v

def Control.Valid (S : Finset ℕ) : Control → Prop
  | .done => True
  | .step a rest => a.Valid S ∧ rest.Valid S
  | .positive source yes no => source∈S ∧ yes.Valid S ∧ no.Valid S

def Control.WidthTrace (S : Finset ℕ) (B : ℕ) : Control → (ℕ→Parts) → Prop
  | .done,v => WidthBank S B v
  | .step a rest,v => WidthBank S B v ∧ a.LiteralFits B ∧ rest.WidthTrace S B (a.update v)
  | .positive source yes no,v => WidthBank S B v ∧
      if 0<(v source).value then yes.WidthTrace S B v else no.WidthTrace S B v

def Control.AdmissibleTrace : Control → (ℕ→Parts) → Prop
  | .done,_ => True
  | .step a rest,v => a.Admissible v ∧ rest.AdmissibleTrace (a.update v)
  | .positive source yes no,v =>
      if 0<(v source).value then yes.AdmissibleTrace v else no.AdmissibleTrace v

theorem Control.evaluate_good (S : Finset ℕ) (c : Control) (hc : c.Valid S)
    (v : ℕ→Parts) (hv : Good S v) (ha : c.AdmissibleTrace v) : Good S (c.evaluate v) := by
  induction c generalizing v with
  | done => exact hv
  | step a rest ih => exact ih hc.2 (a.update v) (a.update_good S hc.1 v hv ha.1) ha.2
  | positive source yes no iy ino =>
    by_cases hp : 0<(v source).value
    · simpa only [Control.evaluate,hp,ite_true] using iy hc.2.1 v hv (by simpa [Control.AdmissibleTrace,hp] using ha)
    · simpa only [Control.evaluate,hp,ite_false] using ino hc.2.2 v hv (by simpa [Control.AdmissibleTrace,hp] using ha)

theorem Control.evaluate_value (S : Finset ℕ) (c : Control) (hc : c.Valid S)
    (v : ℕ→Parts) (hv : Good S v) (ha : c.AdmissibleTrace v) :
    valueBank (c.evaluate v)=c.rationalEvaluate (valueBank v) := by
  induction c generalizing v with
  | done => rfl
  | step a rest ih =>
    change valueBank (rest.evaluate (a.update v))=rest.rationalEvaluate (a.rationalUpdate (valueBank v))
    rw [ih hc.2 (a.update v) (a.update_good S hc.1 v hv ha.1) ha.2,a.update_value S hc.1 v hv ha.1]
  | positive source yes no iy ino =>
    by_cases hp : 0<(v source).value
    · simpa only [Control.evaluate,Control.rationalEvaluate,valueBank,hp,ite_true] using
        iy hc.2.1 v hv (by simpa [Control.AdmissibleTrace,hp] using ha)
    · simpa only [Control.evaluate,Control.rationalEvaluate,valueBank,hp,ite_false] using
        ino hc.2.2 v hv (by simpa [Control.AdmissibleTrace,hp] using ha)

theorem Control.executes (S : Finset ℕ) (c : Control) (hc : c.Valid S)
    (v : ℕ→Parts) (B : ℕ) (hw : c.WidthTrace S B v) (hg : Good S v) (ha : c.AdmissibleTrace v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape c.code cost s t ∧ cost≤c.steps*operationCost B+1 ∧
      Ready S (c.evaluate v) t ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  induction c generalizing v s with
  | done => exact ⟨1,s,.skip s,by simp [Control.steps],hs,BinaryPrecision.Frame.refl _ _⟩
  | step a rest ih =>
    obtain ⟨c0,s0,e0,h0,b0,f0⟩ := a.executes S hc.1 v B hw.1 hw.2.1 input tape s hs
    obtain ⟨c1,t,e1,h1,b1,f1⟩ := ih hc.2 (a.update v) hw.2.2
      (a.update_good S hc.1 v hg ha.1) ha.2 s0 b0
    refine ⟨c0+c1,t,e0.seq e1,?_,b1,f0.trans f1⟩
    simp only [Control.steps,Nat.add_mul,Nat.one_mul]
    omega
  | positive source yes no iy ino =>
    obtain ⟨c0,s0,e0,h0,b0,z0,f0,sg⟩ := positivePrefix_executes S source hc.1 v B hw.1
      (hg source hc.1) input tape s hs
    obtain ⟨c1,s1,e1,h1,b1,f1⟩ := positiveCleanup_executes S source hc.1 v B hw.1 input tape s0 b0 z0
    have htest : c0+(1+c1)≤operationCost B := by have hh := inverse_cost B; omega
    by_cases hp : 0<(v source).value
    · obtain ⟨c2,t,e2,h2,b2,f2⟩ := iy hc.2.1 v
        (by simpa only [Control.WidthTrace,hp,ite_true] using hw.2) hg
        (by simpa only [Control.AdmissibleTrace,hp,ite_true] using ha) s1 b1
      have hsg : s0.val.registers 23=true := by simpa only [hp,decide_true] using sg
      refine ⟨c0+(1+(c1+c2)),t,e0.seq (Executes.yes hsg (e1.seq e2)),?_,?_,f0.trans (f1.trans f2)⟩
      · have hm := Nat.mul_le_mul_right (operationCost B) (le_max_left yes.steps no.steps)
        simp only [Control.steps,Nat.add_mul,Nat.one_mul]
        omega
      · simpa only [Control.evaluate,hp,ite_true] using b2
    · obtain ⟨c2,t,e2,h2,b2,f2⟩ := ino hc.2.2 v
        (by simpa only [Control.WidthTrace,hp,ite_false] using hw.2) hg
        (by simpa only [Control.AdmissibleTrace,hp,ite_false] using ha) s1 b1
      have hsg : s0.val.registers 23=false := by simpa only [hp,decide_false] using sg
      refine ⟨c0+(1+(c1+c2)),t,e0.seq (Executes.no hsg (e1.seq e2)),?_,?_,f0.trans (f1.trans f2)⟩
      · have hm := Nat.mul_le_mul_right (operationCost B) (le_max_right yes.steps no.steps)
        simp only [Control.steps,Nat.add_mul,Nat.one_mul]
        omega
      · simpa only [Control.evaluate,hp,ite_false] using b2

theorem Control.computes (S : Finset ℕ) (c : Control) (hc : c.Valid S)
    (v : ℕ→Parts) (B : ℕ) (hw : c.WidthTrace S B v) (hg : Good S v) (ha : c.AdmissibleTrace v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t output,
      (runPriced (c.code.compile.next input tape) (c.steps*operationCost B+2) s.val).finished=
        some (t.place c.code.size) ∧
      (runPriced (c.code.compile.next input tape) (c.steps*operationCost B+2) s.val).instructions=cost ∧
      cost≤c.steps*operationCost B+1 ∧ Ready S output t ∧ Good S output ∧
      valueBank output=c.rationalEvaluate (valueBank v) := by
  obtain ⟨cost,t,he,hcost,hb,_⟩ := c.executes S hc v B hw hg ha input tape s hs
  obtain ⟨hrun,hc'⟩ := he.compiled_run (c.steps*operationCost B+2) (by omega)
  exact ⟨cost,t,c.evaluate v,hrun,hc',hcost,hb,c.evaluate_good S hc v hg ha,c.evaluate_value S hc v hg ha⟩

def Control.prepend (ins : List Instruction) (tail : Control) : Control := ins.foldr .step tail

theorem Control.prepend_steps (ins : List Instruction) (tail : Control) :
    (tail.prepend ins).steps=ins.length+tail.steps := by
  induction ins with
  | nil => simp [Control.prepend]
  | cons a rest ih =>
    simp only [Control.prepend,List.foldr_cons,Control.steps,List.length_cons] at *
    omega

theorem Control.prepend_evaluate (ins : List Instruction) (tail : Control) (v : ℕ→Parts) :
    (tail.prepend ins).evaluate v=tail.evaluate (RationalDataflow.evaluate ins v) := by
  induction ins generalizing v with
  | nil => rfl
  | cons a rest ih => exact ih (a.update v)

#print axioms Control.computes

end Maxwell.Continuum.RationalDataflow
