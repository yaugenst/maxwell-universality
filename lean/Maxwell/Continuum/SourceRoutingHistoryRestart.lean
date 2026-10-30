import Maxwell.Continuum.SourceRoutingHistoryGenerate

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
open Structured Maxwell.Logical.Routing GeometryArithmetic
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def Plan.following {q : ℕ} (p : Plan q) : Plan q := ⟨p.slab (2*q+1),p.clock,p.positive,p.clock_length⟩
def restart : List NatAssign.Instruction :=
  [.copy 1200 1225,.multiply 1200 1225,.multiply 1217 1225,
    .copy 1216 1215,.add 1225 1216,.literal 1202 1,.literal 1225 0]

theorem restart_values {q : ℕ} (p : Plan q) :
    NatAssign.values restart (GeometrySort.seed (p.layer (2*q)) (2*q+1) 0)=
      GeometrySort.seed (p.following.layer 0) 1 0 := by
  funext j
  simp only [restart,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target]
  by_cases h25 : j=1225
  · subst j;simp [GeometrySort.seed]
  by_cases h2 : j=1202
  · subst j;simp [GeometrySort.seed]
  by_cases h16 : j=1216
  · subst j;simp [GeometrySort.seed,Plan.layer,Plan.slab,Plan.stride,Plan.width,GeometrySort.Plan.width,Plan.following];ring
  by_cases h15 : j=1215
  · subst j;simp [GeometrySort.seed,Plan.layer,Plan.slab,Plan.following]
  simp only [Function.update_of_ne h25,Function.update_of_ne h2,
    Function.update_of_ne h16,Function.update_of_ne h15,GeometrySort.seed,h2,h15,h16,ite_false]
  rfl

theorem restart_executes {q : ℕ} (p : Plan q) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed (p.layer (2*q)) (2*q+1) 0) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape (NatAssign.code restart) steps s t ∧ steps ≤ 2^40*(p.bound+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed (p.following.layer 0) 1 0) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame GeometryArithmetic.work s.val t.val := by
  have width:=GeometrySort.seed_width (p.layer (2*q)) (2*q+1) 0 (Nat.zero_le _)
  obtain ⟨steps,t,he,hc,bt,zt,ft⟩:=stage restart
    (by simp [restart,NatAssign.Instruction.Valid,GeometryArithmetic.ids,GeometryArithmetic.controls])
    (GeometrySort.seed (p.layer (2*q)) (2*q+1) 0) p.bound
    (fun j hj => (width j hj).trans (p.layer_bound (2*q) le_rfl))
    (by simp [restart,NatAssign.Instruction.literalWidth,Plan.bound]) input tape s bank ready
  refine ⟨steps,t,he,?_,by simpa only [restart_values] using bt,zt,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by decide)) privateBlank,ft.mono ?_⟩
  · change steps ≤ 3000*8^7*(p.bound+2)^2 at hc
    calc
      steps ≤ 3000*8^7*(p.bound+2)^2 := hc
      _ ≤ 3000*8^7*(p.bound+3)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ 2^40*(p.bound+3)^2 := Nat.mul_le_mul_right _ (by decide)
  · intro j hj
    simp only [GeometryArithmetic.work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms restart_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
