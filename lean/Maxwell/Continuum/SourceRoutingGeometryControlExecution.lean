import Maxwell.Continuum.SourceRoutingGeometryControlBounds

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

theorem Control.executes (c : Control) (valid : c.Valid) (v : ℕ→ℕ)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (admissible : c.Admissible v) (B : ℕ) (width : ∀j∈ids,(v j).bits.length ≤ B)
    (literals : c.Literals B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape c.code steps s t ∧ steps ≤ controlCost c.steps B ∧
      NatAssign.Bank ids (c.evaluate v) t.val ∧ GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧
      BinaryPrecision.Frame work s.val t.val := by
  induction c generalizing v B s with
  | done => exact ⟨1,s,.skip s,controlCost_one _ _,bank,ready,privateBlank,BinaryPrecision.Frame.refl _ _⟩
  | assign a rest ih =>
    have av:=instruction_valid valid.1
    obtain ⟨ca,u,ea,ha,bu,zu,fu⟩:=stage [a] (by intro b hb;obtain rfl:=List.mem_singleton.mp hb;exact av)
      v B width (by intro b hb;obtain rfl:=List.mem_singleton.mp hb;exact literals.1) input tape s bank ready
    have wu:=NatAssign.instruction_width ids a av v B width literals.1
    have pu:=RationalAccumulator.blank_of_eq (fu.tapes 1249 (by decide)) privateBlank
    obtain ⟨cr,t,er,hr,bt,zt,pt,ft⟩:=ih valid.2 (a.update v) (instruction_zero valid.1 v zero)
      admissible (2*B+1) wu (literals.2.mono (by omega)) u bu zu pu
    have first : ca ≤ 2^104*(B+2)^2 := ha.trans (Nat.mul_le_mul_right _ (by
      change 3000*8^1 ≤ 2^104
      decide))
    have frame : BinaryPrecision.Frame work s.val u.val := fu.mono (by
      intro j hj
      simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
      tauto)
    exact ⟨ca+cr,t,ea.seq er,controlCost_successor rest.steps B ca cr first hr,bt,zt,pt,frame.trans ft⟩
  | divide source divisor quotient remainder rest ih =>
    obtain ⟨ca,u,ea,ha,bu,zu,pu,fu⟩:=GeometryArithmetic.divide source divisor quotient remainder
      valid.1 valid.2.1 valid.2.2.1 valid.2.2.2.1 valid.2.2.2.2.1
      v zero admissible.1 B width input tape s bank ready privateBlank
    have wu:=divided_width v source divisor quotient remainder B (Finset.mem_union_left _ valid.1) width
    have qu:=divided_zero v source divisor quotient remainder valid.2.2.1 valid.2.2.2.1 zero
    obtain ⟨cr,t,er,hr,bt,zt,pt,ft⟩:=ih valid.2.2.2.2.2 (divided v source divisor quotient remainder)
      qu admissible.2 (2*B+1) (fun j hj => (wu j hj).trans (by omega))
      (literals.mono (by omega)) u bu zu pu
    have power : 1 ≤ (B+2)^2 := Nat.succ_le_of_lt (by positivity)
    have first : ca ≤ 2^104*(B+2)^2 := by nlinarith only [ha,power]
    exact ⟨ca+cr,t,ea.seq er,controlCost_successor rest.steps B ca cr first hr,bt,zt,pt,fu.trans ft⟩
  | decrement target rest ih =>
    obtain ⟨ca,u,ea,ha,bu,zu,pu,fu⟩:=GeometryArithmetic.decrement target valid.1 v admissible.1
      input tape s bank ready privateBlank
    have wu:=decrement_width v target B (Finset.mem_union_left _ valid.1) width
    obtain ⟨cr,t,er,hr,bt,zt,pt,ft⟩:=ih valid.2 (Function.update v target (v target-1))
      (decrement_zero v target valid.1 zero) admissible.2 (2*B+1)
      (fun j hj => (wu j hj).trans (by omega)) (literals.mono (by omega)) u bu zu pu
    have wt:=width target (Finset.mem_union_left _ valid.1)
    have linear : 29*B+31 ≤ 32*(B+2)^2 := by nlinarith
    have first : ca ≤ 2^104*(B+2)^2 := by
      exact (show ca ≤ 32*(B+2)^2 by omega).trans (Nat.mul_le_mul_right _ (by decide))
    exact ⟨ca+cr,t,ea.seq er,controlCost_successor rest.steps B ca cr first hr,bt,zt,pt,fu.trans ft⟩
  | positive source yes no iy ino =>
    let u:=positiveState source s
    have zu : GeometryArray.Ready u.val := ⟨ready.scratch,ready.seven,ready.pack⟩
    have ea:=positive_executes source input tape s
    have flag:=positive_flag source (v source) s (bank source (Finset.mem_union_left _ valid.1))
    have wu : ∀j∈ids,(v j).bits.length ≤ 2*B+1 := fun j hj => (width j hj).trans (by omega)
    have overhead : 4 ≤ 2^104*(B+2)^2 := by
      have h : 1 ≤ (B+2)^2 := Nat.succ_le_of_lt (by positivity)
      nlinarith only [h]
    by_cases hp : 0<v source
    · obtain ⟨cr,t,er,hr,bt,zt,pt,ft⟩:=iy valid.2.1 v zero
        (by simpa only [Control.Admissible,hp,ite_true] using admissible) (2*B+1) wu
        (literals.1.mono (by omega)) u bank zu privateBlank
      have hf : u.val.registers 23=true := by simpa only [hp,decide_true] using flag
      refine ⟨3+(1+cr),t,ea.seq (Executes.yes hf er),?_,?_,zt,pt,(positive_frame source s).trans ft⟩
      · have h:=controlCost_successor (max yes.steps no.steps) B 4 cr overhead
          (hr.trans (controlCost_steps _ _ _ (le_max_left _ _)))
        change 3+(1+cr) ≤ controlCost (1+max yes.steps no.steps) B
        omega
      · simpa only [Control.evaluate,hp,ite_true] using bt
    · obtain ⟨cr,t,er,hr,bt,zt,pt,ft⟩:=ino valid.2.2 v zero
        (by simpa only [Control.Admissible,hp,ite_false] using admissible) (2*B+1) wu
        (literals.2.mono (by omega)) u bank zu privateBlank
      have hf : u.val.registers 23=false := by simpa only [hp,decide_false] using flag
      refine ⟨3+(1+cr),t,ea.seq (Executes.no hf er),?_,?_,zt,pt,(positive_frame source s).trans ft⟩
      · have h:=controlCost_successor (max yes.steps no.steps) B 4 cr overhead
          (hr.trans (controlCost_steps _ _ _ (le_max_right _ _)))
        change 3+(1+cr) ≤ controlCost (1+max yes.steps no.steps) B
        omega
      · simpa only [Control.evaluate,hp,ite_false] using bt

#print axioms Control.executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
