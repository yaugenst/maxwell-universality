import Maxwell.Continuum.SourceRoutingPathRetreat
import Maxwell.Continuum.SourceRoutingHistoryRestart

/-! At a reverse phase boundary, the preceding history ends one slab before
the current history starts. Restore its final round and retreat once. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
open Structured GeometryArithmetic
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def restartRound : List NatAssign.Instruction :=
  [.copy 1200 1202,.multiply 1220 1202,.add 1220 1202]
def restartCode : Code := .seq (NatAssign.code restartRound) retreat.code
def restartCost {q : ℕ} (p : GeometryHistory.Plan q) : ℕ :=
  2^24*((p.following.layer 0).bound 1+3)^2+2^152*((p.layer (2*q+1)).bound (2*q+2)+2)^2

theorem restartRound_values {q : ℕ} (p : GeometryHistory.Plan q) (index : ℕ) :
    NatAssign.values restartRound (GeometrySort.seed (p.following.layer 0) 1 index)=
      GeometrySort.seed (p.layer (2*q+1)) (2*q+2) index := by
  funext j
  by_cases same : j=1202
  · subst j
    simp [restartRound,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,GeometrySort.seed]
    omega
  simp only [restartRound,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_of_ne same,
    GeometrySort.seed,same,ite_false]
  have source : (p.following.layer 0).source=(p.layer (2*q+1)).source := by
    simp [GeometryHistory.Plan.layer,GeometryHistory.Plan.slab,GeometryHistory.Plan.following]
  have destination : (p.following.layer 0).destination=(p.layer (2*q+1)).destination := by
    simp [GeometryHistory.Plan.layer,GeometryHistory.Plan.slab,GeometryHistory.Plan.following,
      GeometryHistory.Plan.stride,GeometryHistory.Plan.width]
    ring
  rw [source,destination]
  rfl

theorem restart_executes {q : ℕ} (p : GeometryHistory.Plan q) (index : ℕ) (indexBound : index ≤ q*q)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids (GeometrySort.seed (p.following.layer 0) 1 index) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape restartCode steps s t ∧ steps ≤ restartCost p ∧
      NatAssign.Bank ids (GeometrySort.seed (p.layer (2*q)) (2*q+1) index) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c₀,a,e₀,h₀,ba,za,f₀⟩ := stage restartRound
    (by simp [restartRound,NatAssign.Instruction.Valid,ids,controls]) _ ((p.following.layer 0).bound 1)
    (GeometrySort.seed_width _ _ _ indexBound)
    (by simp [restartRound,NatAssign.Instruction.literalWidth]) input tape s bank ready
  rw [restartRound_values] at ba
  obtain ⟨c₁,t,e₁,h₁,bt,zt,pt,f₁⟩ := retreat_executes p (2*q) index indexBound input tape a ba za
    (RationalAccumulator.blank_of_eq (f₀.tapes 1249 (by decide)) privateBlank)
  refine ⟨c₀+c₁,t,e₀.seq e₁,?_,bt,zt,pt,(f₀.mono ?_).trans f₁⟩
  · have first : c₀ ≤ 2^24*((p.following.layer 0).bound 1+3)^2 := calc
      c₀ ≤ 3000*8^3*((p.following.layer 0).bound 1+2)^2 := h₀
      _ ≤ 2^24*((p.following.layer 0).bound 1+3)^2 :=
        Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (by omega) 2)
    dsimp only [restartCost]
    omega
  · intro j hj
    simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms restart_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPathReverse
