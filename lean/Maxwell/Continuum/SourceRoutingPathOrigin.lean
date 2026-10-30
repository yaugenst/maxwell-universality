import Maxwell.Continuum.SourceRoutingPathChoice
import Maxwell.Continuum.SourceRoutingPathAdvance

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def originScale (transpose : Bool) : Control := Control.prepend
  ([.multiply 1229 1226,.multiply 1229 1227,.multiply 1229 1228]++
    if transpose then [.copy 1226 1230,.copy 1227 1226,.copy 1230 1227,.literal 1230 0] else []) .done

def originProgram (transpose : Bool) : Control := Control.prepend
  [.literal 1229 16,.copy 1203 1226,.copy 1204 1227,.copy 1233 1228]
  (.positive 1212 (.assign (.copy 1213 1226) (originScale transpose)) (originScale transpose))

def originColumn (v : ℕ→ℕ) : ℕ := if 0<v 1212 then v 1213 else v 1203

theorem origin_valid (transpose : Bool) : (originProgram transpose).Valid := by
  cases transpose <;> simp [originProgram,originScale,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]

theorem origin_steps (transpose : Bool) : (originProgram transpose).steps ≤ 14 := by
  cases transpose <;> decide

theorem origin_literals (transpose : Bool) (B : ℕ) (large : 5 ≤ B) : (originProgram transpose).Literals B := by
  cases transpose <;> simp [originProgram,originScale,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth]
  all_goals exact large

theorem origin_admissible (transpose : Bool) (v : ℕ→ℕ) : (originProgram transpose).Admissible v := by
  cases transpose <;> simp [originProgram,originScale,Control.Admissible,Control.prepend]

theorem origin_values (transpose : Bool) (v : ℕ→ℕ) :
    (originProgram transpose).evaluate v 1226=16*(if transpose then v 1204 else originColumn v) ∧
    (originProgram transpose).evaluate v 1227=16*(if transpose then originColumn v else v 1204) ∧
    (originProgram transpose).evaluate v 1228=16*v 1233 := by
  cases transpose <;> by_cases flag : 0<v 1212 <;>
    simp [originProgram,originScale,originColumn,Control.evaluate,Control.prepend,
      NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,flag]

theorem origin_other (transpose : Bool) (v : ℕ→ℕ) (j : ℕ) (outside : j∉({1226,1227,1228,1229,1230} : Finset ℕ)) :
    (originProgram transpose).evaluate v j=v j := by
  apply Control.evaluate_other
  intro h
  exact outside ((show (originProgram transpose).writes⊆{1226,1227,1228,1229,1230} by cases transpose <;> decide) h)

theorem origin_width (transpose : Bool) (v : ℕ→ℕ) (B : ℕ) (large : 5 ≤ B)
    (width : ∀j∈ids,(v j).bits.length ≤ B) :
    ∀j∈ids,((originProgram transpose).evaluate v j).bits.length ≤ 2^14*(B+1) := by
  have h:=(originProgram transpose).evaluate_width (origin_valid transpose) v B width (origin_literals transpose B large)
  intro j hj
  exact (Nat.le_add_right _ _).trans ((h j hj).trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by decide) (origin_steps transpose))))

theorem origin_executes (transpose : Bool) (v : ℕ→ℕ) (B : ℕ) (large : 5 ≤ B)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (width : ∀j∈ids,(v j).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape (originProgram transpose).code steps s t ∧
      steps ≤ 2^152*(B+2)^2 ∧ NatAssign.Bank ids ((originProgram transpose).evaluate v) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,zt,t1249,ft⟩:=(originProgram transpose).executes (origin_valid transpose) v zero
    (origin_admissible transpose v) B width (origin_literals transpose B large) input tape s bank ready privateBlank
  exact ⟨steps,t,he,hc.trans (controlCost_steps _ _ _ (origin_steps transpose)),bt,zt,t1249,ft⟩

#print axioms origin_values
#print axioms origin_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
