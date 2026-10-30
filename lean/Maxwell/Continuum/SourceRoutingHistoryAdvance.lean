import Maxwell.Continuum.SourceRoutingHistoryLayout

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
open Structured Maxwell.Logical.Routing GeometryArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def advance : List NatAssign.Instruction :=
  [.copy 1200 1225,.multiply 1200 1225,.multiply 1217 1225,
    .copy 1216 1215,.add 1225 1216,.literal 1201 0,.add 1219 1202,.literal 1225 0]

theorem advance_values {q : ℕ} (p : Plan q) (k : ℕ) :
    NatAssign.values advance (GeometrySort.seed (p.layer k) (k+1) (q*q))=
      GeometrySort.seed (p.layer (k+1)) (k+2) 0 := by
  funext j
  simp only [advance,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target]
  by_cases h25 : j=1225
  · subst j;simp [GeometrySort.seed]
  by_cases h2 : j=1202
  · subst j;simp [GeometrySort.seed];omega
  by_cases h1 : j=1201
  · subst j;simp [GeometrySort.seed]
  by_cases h16 : j=1216
  · subst j;simp [GeometrySort.seed,Plan.layer,Plan.slab,Plan.stride,Plan.width,GeometrySort.Plan.width];ring
  by_cases h15 : j=1215
  · subst j;simp [GeometrySort.seed,Plan.layer]
  simp only [Function.update_of_ne h25,Function.update_of_ne h2,Function.update_of_ne h1,
    Function.update_of_ne h16,Function.update_of_ne h15,GeometrySort.seed,h1,h2,h15,h16,ite_false]
  rfl

theorem advance_valid : ∀a∈advance,a.Valid GeometryArithmetic.ids := by
  simp [advance,NatAssign.Instruction.Valid,GeometryArithmetic.ids,GeometryArithmetic.controls]

theorem advance_executes {q : ℕ} (p : Plan q) (k : ℕ) (hk : k ≤ 2*q)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed (p.layer k) (k+1) (q*q)) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : RationalAccumulator.Blank s.val 1249) :
    ∃steps t,Executes input tape (NatAssign.code advance) steps s t ∧
      steps ≤ 2^40*(p.bound+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed (p.layer (k+1)) (k+2) 0) t.val ∧
      GeometryArray.Ready t.val ∧ RationalAccumulator.Blank t.val 1249 ∧
      BinaryPrecision.Frame GeometryArithmetic.work s.val t.val := by
  have width := GeometrySort.seed_width (p.layer k) (k+1) (q*q) le_rfl
  obtain ⟨steps,t,he,hc,bt,zt,ft⟩:=stage advance advance_valid
    (GeometrySort.seed (p.layer k) (k+1) (q*q)) p.bound
    (fun j hj => (width j hj).trans (p.layer_bound k hk))
    (by simp [advance,NatAssign.Instruction.literalWidth]) input tape s bank ready
  refine ⟨steps,t,he,?_,by simpa only [advance_values] using bt,zt,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by decide)) privateBlank,ft.mono ?_⟩
  · change steps ≤ 3000*8^8*(p.bound+2)^2 at hc
    calc
      steps ≤ 3000*8^8*(p.bound+2)^2 := hc
      _ ≤ 3000*8^8*(p.bound+3)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ 2^40*(p.bound+3)^2 := Nat.mul_le_mul_right _ (by decide)
  · intro j hj
    simp only [GeometryArithmetic.work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms advance_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryHistory
