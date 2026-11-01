import Maxwell.Continuum.SourceRoutingPathRestore

/-! Cross from the left paired top port to its adjacent right port.
The top connector has already emitted the intervening lattice samples. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def pairSwitch : List NatAssign.Instruction := [.add 1200 1201]

theorem pairSwitch_values {half : ℕ} (p : GeometrySort.Plan (2*half)) (round : ℕ)
    (pair : Fin half × Fin (2*half)) :
    NatAssign.values pairSwitch (GeometrySort.seed p round (finProdFinEquiv (Gluing.pairPort pair false)).val)=
      GeometrySort.seed p round (finProdFinEquiv (Gluing.pairPort pair true)).val := by
  funext j
  by_cases same : j=1201
  · subst j
    simp [pairSwitch,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,GeometrySort.seed,Gluing.pairPort,finProdFinEquiv]
    ring
  · simp [pairSwitch,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,GeometrySort.seed,same]

theorem pairSwitch_executes {half : ℕ} (p : GeometrySort.Plan (2*half)) (round : ℕ)
    (pair : Fin half × Fin (2*half)) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed p round (finProdFinEquiv (Gluing.pairPort pair false)).val) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape (NatAssign.code pairSwitch) steps s t ∧
      steps ≤ 2^16*(p.bound round+2)^2 ∧
      NatAssign.Bank ids (GeometrySort.seed p round (finProdFinEquiv (Gluing.pairPort pair true)).val) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,zt,ft⟩ := stage pairSwitch
    (by simp [pairSwitch,NatAssign.Instruction.Valid,ids,controls])
    (GeometrySort.seed p round (finProdFinEquiv (Gluing.pairPort pair false)).val) (p.bound round)
    (GeometrySort.seed_width p round _ (finProdFinEquiv (Gluing.pairPort pair false)).isLt.le)
    (by simp [pairSwitch,NatAssign.Instruction.literalWidth]) input tape s bank ready
  refine ⟨steps,t,he,hc.trans (Nat.mul_le_mul_right _ (by decide)),?_,zt,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by decide)) privateBlank,ft.mono ?_⟩
  · simpa only [pairSwitch_values] using bt
  · intro j hj
    simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms pairSwitch_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
