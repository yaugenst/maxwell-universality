import Maxwell.Continuum.SourceRoutingGeometryControlValues
import Maxwell.Continuum.SourceRoutingPhaseKeys

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured GeometryArithmetic Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def rightPartner : Control := .positive 1203
  (.assign (.copy 1203 1210) (.decrement 1210
    (Control.prepend [.multiply 1200 1210,.add 1204 1210,.literal 1211 1] .done))) .done

def leftPartner : Control := Control.prepend [.copy 1207 1222,.add 1219 1222]
  (.divide 1200 1222 1223 1224 (.positive 1223 (.assign (.add 1200 1210) .done) .done))

def choosePartner : Control := .positive 1206
  (.positive 1205 rightPartner leftPartner) (.positive 1205 leftPartner rightPartner)

def partnerPrepare : List NatAssign.Instruction :=
  [.copy 1201 1210,.literal 1211 0,.copy 1203 1207,.add 1219 1207]

def partnerProgram : Control := .divide 1201 1200 1203 1204
  (.divide 1203 1220 1221 1205 (.divide 1202 1220 1221 1206
    (Control.prepend partnerPrepare choosePartner)))

def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values partnerPrepare
  (divided (divided (divided v 1201 1200 1203 1204) 1203 1220 1221 1205) 1202 1220 1221 1206)

theorem program_evaluate (v : ℕ→ℕ) : partnerProgram.evaluate v=choosePartner.evaluate (prepared v) := rfl

theorem partner_valid : partnerProgram.Valid := by
  simp [partnerProgram,partnerPrepare,choosePartner,rightPartner,leftPartner,Control.Valid,Control.prepend,
    NatAssign.Instruction.Valid,controls]

theorem partner_steps : partnerProgram.steps ≤ 20 := by decide
theorem partner_literals (B : ℕ) (hB : 1 ≤ B) : partnerProgram.Literals B := by
  simp [partnerProgram,partnerPrepare,choosePartner,rightPartner,leftPartner,Control.Literals,Control.prepend,
    NatAssign.Instruction.literalWidth]
  exact hB

theorem right_admissible (v : ℕ→ℕ) : rightPartner.Admissible v := by
  simp [rightPartner,Control.Admissible,Control.prepend,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target]

theorem left_admissible (v : ℕ→ℕ) (hone : v 1219=1) : leftPartner.Admissible v := by
  simp [leftPartner,Control.Admissible,Control.prepend,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,hone]

theorem right_result (v : ℕ→ℕ) :
    (rightPartner.evaluate v 1210,rightPartner.evaluate v 1211)=
      if 0<v 1203 then (v 1200*(v 1203-1)+v 1204,1) else (v 1210,v 1211) := by
  simp only [rightPartner,Control.evaluate]
  split_ifs <;> simp [Control.prepend,Control.evaluate,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Nat.add_comm]

theorem left_result (v : ℕ→ℕ) (hone : v 1219=1) :
    (leftPartner.evaluate v 1210,leftPartner.evaluate v 1211)=
      if v 1207<v 1200 then (v 1210+v 1200,v 1211) else (v 1210,v 1211) := by
  have quotient : 0<v 1200/(1+v 1207) ↔ v 1207<v 1200 := by
    constructor
    · intro h
      by_contra hh
      have hz:=Nat.div_eq_of_lt (show v 1200<1+v 1207 by omega)
      omega
    · intro h
      exact Nat.div_pos (by omega) (by omega)
  let u:=NatAssign.values [.copy 1207 1222,.add 1219 1222] v
  let d:=divided u 1200 1222 1223 1224
  have evaluated : leftPartner.evaluate v=
      (Control.positive 1223 (.assign (.add 1200 1210) .done) .done).evaluate d := rfl
  have flag : 0<d 1223 ↔ v 1207<v 1200 := by
    change 0<v 1200/(v 1219+v 1207) ↔ v 1207<v 1200
    rw [hone]
    exact quotient
  by_cases hp : v 1207<v 1200
  · rw [evaluated,Control.positive_true _ _ _ _ (flag.mpr hp)]
    simp [Control.evaluate,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,d,u,divided,NatAssign.values,hp,Nat.add_comm]
  · rw [evaluated,Control.positive_false _ _ _ _ (fun h => hp (flag.mp h))]
    simp [Control.evaluate,d,u,divided,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target,hp]

structure PartnerSetup (q index round : ℕ) (v : ℕ→ℕ) : Prop where
  count : v 1200=q
  cursor : v 1201=index
  layer : v 1202=round
  one : v 1219=1
  two : v 1220=2

theorem prepared_fields {q index round : ℕ} {v : ℕ→ℕ} (setup : PartnerSetup q index round v) :
    prepared v 1200=q ∧ prepared v 1203=index/q ∧ prepared v 1204=index%q ∧
    prepared v 1205=(index/q)%2 ∧ prepared v 1206=round%2 ∧ prepared v 1207=index/q+1 ∧
    prepared v 1210=index ∧ prepared v 1211=0 ∧ prepared v 1219=1 := by
  simp [prepared,partnerPrepare,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,
    setup.count,setup.cursor,setup.layer,setup.one,setup.two,Nat.add_comm]

#print axioms partner_valid
#print axioms right_result
#print axioms left_result
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
