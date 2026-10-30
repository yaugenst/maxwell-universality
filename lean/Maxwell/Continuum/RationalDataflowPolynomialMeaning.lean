import Maxwell.Continuum.RationalDataflowPolynomialPlan

/-! Exact rational meaning of the fixed polynomial-query schedule. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 32768

theorem horner_iterate_entry {n : ℕ} (a : Table n) (v : ℕ→Parts) :
    iterate a 1 hornerBody (sumStart v 0) n 1=if n=0 then v 1 else a.getD 0 := by
  cases n with
  | zero => simp only [iterate,sumStart,Function.update_of_ne (by decide : (1:ℕ)≠0),ite_true]
  | succ n =>
    simp only [iterate,hornerBody,Control.evaluate,Instruction.update,
      Function.update_of_ne (by decide : (1:ℕ)≠0),Function.update_self]
    simp

theorem horner_iterate_state {n : ℕ} (a : Table n) (v : ℕ→Parts) :
    iterate a 1 hornerBody (sumStart v 0) n=
      Function.update (Function.update v 1 (if n=0 then v 1 else a.getD 0)) 0 (reverseHorner a (v 2) n) := by
  funext i
  by_cases h0 : i=0
  · subst i
    rw [Function.update_self,horner_iterate_accumulator]
  · rw [Function.update_of_ne h0]
    by_cases h1 : i=1
    · subst i
      rw [Function.update_self,horner_iterate_entry]
    · rw [Function.update_of_ne h1,horner_iterate_keep a v n i h0 h1]

def polynomialValue {n : ℕ} (a : Table n) (x : ℚ) : ℚ :=
  ∑ i : Fin n, (a.get i).value*x^i.val

def primitiveValue {n : ℕ} (a : Table n) (x : ℚ) : ℚ := x*polynomialValue a (x*x)

def antiderivativeRationalState {n : ℕ} (a : Table n) (point target : ℕ) (v : ℕ→ℚ) : ℕ→ℚ :=
  Function.update
    (Function.update (Function.update (Function.update v 2 (v point*v point))
      1 (if n=0 then v 1 else (a.getD 0).value)) 0 (polynomialValue a (v point*v point)))
    target (primitiveValue a (v point))

theorem antiderivativeState_value {n : ℕ} (a : Table n) (point target : ℕ)
    (hp0 : point≠0) (hp1 : point≠1) (hp2 : point≠2)
    (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hp : (v point).Valid) :
    valueBank (antiderivativeState a point target v)=
      antiderivativeRationalState a point target (valueBank v) := by
  dsimp only [antiderivativeState]
  rw [horner_iterate_state]
  simp only [Instruction.update,BinaryOp.eval,Function.update_self,
    Function.update_of_ne hp0,Function.update_of_ne hp1,Function.update_of_ne hp2,
    Function.update_of_ne (by decide : (1:ℕ)≠2)]
  simp only [valueBank_update,Parts.mul_value,
    reverseHorner_value a _ ha (Parts.mul_valid hp hp)]
  unfold antiderivativeRationalState primitiveValue polynomialValue
  simp only [valueBank]
  congr 1
  · congr 1
    split_ifs <;> rfl
  · ring

namespace PolynomialStage

def rationalEvaluate {n : ℕ} (a : Table n) : PolynomialStage→(ℕ→ℚ)→(ℕ→ℚ)
  | .arithmetic op,v => op.rationalUpdate v
  | .clamp,v => Calibration.RawCutoff.clampControl.rationalEvaluate v
  | .query point target,v => antiderivativeRationalState a point target v

theorem evaluate_good {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) (op : PolynomialStage) (hop : op.Valid S)
    (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hv : Good S v) (had : op.Admissible v) :
    Good S (op.evaluate a v) := by
  cases op with
  | arithmetic instruction => exact instruction.update_good S hop v hv had
  | clamp =>
    exact Calibration.RawCutoff.clampControl.evaluate_good S
      (Calibration.RawCutoff.clampControl_valid S h0 h1 h2) v hv
      (Calibration.RawCutoff.clampControl_admissible v)
  | query point target =>
    have preValid : (Instruction.binary .mul 2 point point).Valid S := ⟨h2,hop.1,hop.1⟩
    have hg := Instruction.update_good S _ preValid v hv trivial
    have hhorner := horner_iterate_good a S h0 h1 h2 ha _ hg n
    exact Instruction.update_good S (.binary .mul target 0 point) ⟨hop.2.1,h0,hop.1⟩ _ hhorner trivial

theorem evaluate_value {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) (op : PolynomialStage) (hop : op.Valid S)
    (ha : ∀ i, (a.get i).Valid) (v : ℕ→Parts) (hv : Good S v) (had : op.Admissible v) :
    valueBank (op.evaluate a v)=op.rationalEvaluate a (valueBank v) := by
  cases op with
  | arithmetic instruction => exact instruction.update_value S hop v hv had
  | clamp =>
    exact Calibration.RawCutoff.clampControl.evaluate_value S
      (Calibration.RawCutoff.clampControl_valid S h0 h1 h2) v hv
      (Calibration.RawCutoff.clampControl_admissible v)
  | query point target =>
    exact antiderivativeState_value a point target hop.2.2.1 hop.2.2.2.1
      hop.2.2.2.2 ha v (hv point hop.1)
end PolynomialStage

def polynomialPlanRationalEvaluate {n : ℕ} (a : Table n) : List PolynomialStage→(ℕ→ℚ)→(ℕ→ℚ)
  | [],v => v
  | op::rest,v => polynomialPlanRationalEvaluate a rest (op.rationalEvaluate a v)

theorem polynomialPlan_evaluate_good {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) (plan : List PolynomialStage)
    (hvalid : ∀ op∈plan, op.Valid S) (ha : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : Good S v) (had : PolynomialPlanAdmissible a plan v) :
    Good S (polynomialPlanEvaluate a plan v) := by
  induction plan generalizing v with
  | nil => exact hv
  | cons op rest ih =>
    exact ih (fun op hop => hvalid op (by simp [hop])) (op.evaluate a v)
      (op.evaluate_good a S h0 h1 h2 (hvalid op (by simp)) ha v hv had.1) had.2

theorem polynomialPlan_evaluate_value {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S) (plan : List PolynomialStage)
    (hvalid : ∀ op∈plan, op.Valid S) (ha : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : Good S v) (had : PolynomialPlanAdmissible a plan v) :
    valueBank (polynomialPlanEvaluate a plan v)=polynomialPlanRationalEvaluate a plan (valueBank v) := by
  induction plan generalizing v with
  | nil => rfl
  | cons op rest ih =>
    change valueBank (polynomialPlanEvaluate a rest (op.evaluate a v))=_
    rw [ih (fun op hop => hvalid op (by simp [hop])) _
      (op.evaluate_good a S h0 h1 h2 (hvalid op (by simp)) ha v hv had.1) had.2,
      op.evaluate_value a S h0 h1 h2 (hvalid op (by simp)) ha v hv had.1]
    rfl

theorem polynomialPlanEvaluate_append {n : ℕ} (a : Table n) (left right : List PolynomialStage)
    (v : ℕ→Parts) :
    polynomialPlanEvaluate a (left++right) v=
      polynomialPlanEvaluate a right (polynomialPlanEvaluate a left v) := by
  induction left generalizing v with
  | nil => rfl
  | cons op rest ih => exact ih (op.evaluate a v)

theorem polynomialPlanRationalEvaluate_append {n : ℕ} (a : Table n) (left right : List PolynomialStage)
    (v : ℕ→ℚ) :
    polynomialPlanRationalEvaluate a (left++right) v=
      polynomialPlanRationalEvaluate a right (polynomialPlanRationalEvaluate a left v) := by
  induction left generalizing v with
  | nil => rfl
  | cons op rest ih => exact ih (op.rationalEvaluate a v)

theorem polynomialPlanAdmissible_append {n : ℕ} (a : Table n) (left right : List PolynomialStage)
    (v : ℕ→Parts) :
    PolynomialPlanAdmissible a (left++right) v ↔
      PolynomialPlanAdmissible a left v ∧
        PolynomialPlanAdmissible a right (polynomialPlanEvaluate a left v) := by
  induction left generalizing v with
  | nil => simp only [List.nil_append,PolynomialPlanAdmissible,polynomialPlanEvaluate,true_and]
  | cons op rest ih =>
    simp only [List.cons_append,PolynomialPlanAdmissible,polynomialPlanEvaluate,ih,and_assoc]

#print axioms polynomialPlan_evaluate_value
end Maxwell.Continuum.RationalDataflow.PartArray
