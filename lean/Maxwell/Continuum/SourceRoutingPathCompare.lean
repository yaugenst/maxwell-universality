import Maxwell.Continuum.SourceRoutingSortSelection

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def flagBranch : Control := .positive 1223 (.assign (.literal 1212 1) .done) (.assign (.literal 1212 0) .done)
def lessProgram (a b : ℕ) : Control := Control.prepend [.copy a 1222,.add 1219 1222]
  (.divide b 1222 1223 1224 flagBranch)
def compareProgram : Control := .positive 1211 (lessProgram 1208 1209) (lessProgram 1209 1208)

theorem less_result (a b : ℕ) (bNot : b≠1222) (v : ℕ→ℕ) (one : v 1219=1) :
    (lessProgram a b).evaluate v 1212=if v a<v b then 1 else 0 := by
  let d:=divided (NatAssign.values [.copy a 1222,.add 1219 1222] v) b 1222 1223 1224
  have quotient : 0<d 1223 ↔ v a<v b := by
    have denominator : NatAssign.values [.copy a 1222,.add 1219 1222] v 1222=1+v a := by
      simp [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
        NatAssign.Instruction.target,one]
    have numerator : NatAssign.values [.copy a 1222,.add 1219 1222] v b=v b := by
      simp [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,bNot]
    change 0<NatAssign.values [.copy a 1222,.add 1219 1222] v b/
      NatAssign.values [.copy a 1222,.add 1219 1222] v 1222 ↔ _
    rw [denominator,numerator]
    constructor
    · intro h
      by_contra hh
      have hz:=Nat.div_eq_of_lt (show v b<1+v a by omega)
      omega
    · intro h;exact Nat.div_pos (by omega) (by omega)
  change flagBranch.evaluate d 1212=_
  by_cases less : v a<v b
  · rw [show flagBranch.evaluate d=(Control.assign (.literal 1212 1) .done).evaluate d from
      Control.positive_true _ _ _ _ (quotient.mpr less)]
    simp only [less,ite_true]
    rfl
  · rw [show flagBranch.evaluate d=(Control.assign (.literal 1212 0) .done).evaluate d from
      Control.positive_false _ _ _ _ (fun h => less (quotient.mp h))]
    simp only [less,ite_false]
    rfl

theorem compare_result (v : ℕ→ℕ) (one : v 1219=1) :
    compareProgram.evaluate v 1212=
      if (if 0<v 1211 then v 1208<v 1209 else v 1209<v 1208) then 1 else 0 := by
  by_cases flag : 0<v 1211
  · rw [show compareProgram.evaluate v=(lessProgram 1208 1209).evaluate v from
      Control.positive_true _ _ _ _ flag,less_result _ _ (by decide) v one]
    simp only [flag,ite_true]
  · rw [show compareProgram.evaluate v=(lessProgram 1209 1208).evaluate v from
      Control.positive_false _ _ _ _ flag,less_result _ _ (by decide) v one]
    simp only [flag,ite_false]

theorem compare_valid : compareProgram.Valid := by
  simp [compareProgram,lessProgram,flagBranch,Control.Valid,Control.prepend,NatAssign.Instruction.Valid,controls]
theorem compare_steps : compareProgram.steps ≤ 6 := by decide
theorem compare_literals (B : ℕ) (hB : 1 ≤ B) : compareProgram.Literals B := by
  simp [compareProgram,lessProgram,flagBranch,Control.Literals,Control.prepend,NatAssign.Instruction.literalWidth,hB]
theorem compare_admissible (v : ℕ→ℕ) (one : v 1219=1) : compareProgram.Admissible v := by
  simp [compareProgram,lessProgram,flagBranch,Control.Admissible,Control.prepend,
    NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,one]

#print axioms compare_result
#print axioms compare_admissible
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
