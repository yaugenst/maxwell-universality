import Maxwell.Continuum.SourceRoutingPathNextState

/-! Restore the fixed geometry control bank after reading or emitting one
stored layer. This keeps its history addresses and current port unchanged. -/
namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

def seedFields : Finset ℕ := {1200,1201,1202,1215,1216,1217,1219,1220}
def restoreSeed : List NatAssign.Instruction := NatAssign.clearList nextTemporary

theorem restoreSeed_values {q : ℕ} (p : GeometrySort.Plan q) (round index : ℕ) (v : ℕ→ℕ)
    (fields : ∀j∈seedFields,v j=GeometrySort.seed p round index j)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (j : ℕ) (hj : j∈ids) :
    NatAssign.values restoreSeed v j=GeometrySort.seed p round index j := by
  rw [restoreSeed,NatAssign.clearList_values]
  by_cases temporary : j∈nextTemporary
  · rw [ite_eq_left temporary]
    have outside : j≠1200 ∧ j≠1201 ∧ j≠1202 ∧ j≠1215 ∧ j≠1216 ∧ j≠1217 ∧ j≠1219 ∧ j≠1220 := by
      simp only [nextTemporary,List.mem_cons,List.not_mem_nil,or_false] at temporary
      omega
    simp only [GeometrySort.seed,outside.1,outside.2.1,outside.2.2.1,outside.2.2.2.1,
      outside.2.2.2.2.1,outside.2.2.2.2.2.1,outside.2.2.2.2.2.2.1,outside.2.2.2.2.2.2.2,ite_false]
  · rw [ite_eq_right temporary]
    have cases : j∈seedFields ∨ j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts := by
      simp only [ids,controls,Finset.mem_union,Finset.mem_Icc] at hj
      simp only [nextTemporary,List.mem_cons,List.not_mem_nil,or_false,not_or] at temporary
      simp only [seedFields,Finset.mem_insert,Finset.mem_singleton]
      rcases hj with hj|hj
      · omega
      · exact Or.inr hj
    rcases cases with core|natural
    · exact fields j core
    · rw [zero j natural,GeometrySort.seed_zero p round index j natural]

theorem restoreSeed_executes {q : ℕ} (p : GeometrySort.Plan q) (round index B : ℕ) (v : ℕ→ℕ)
    (fields : ∀j∈seedFields,v j=GeometrySort.seed p round index j)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (width : ∀j∈ids,(v j).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (bank : NatAssign.Bank ids v s.val) (ready : GeometryArray.Ready s.val)
    (privateBlank : Blank s.val 1249) :
    ∃steps t,Executes input tape (NatAssign.code restoreSeed) steps s t ∧
      steps ≤ 2^110*(B+2)^2 ∧ NatAssign.Bank ids (GeometrySort.seed p round index) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,zt,ft⟩ := stage restoreSeed
    (by simp [restoreSeed,nextTemporary,NatAssign.clearList,NatAssign.Instruction.Valid,ids,controls]) v B width
    (by simp [restoreSeed,NatAssign.clearList,NatAssign.Instruction.literalWidth]) input tape s bank ready
  refine ⟨steps,t,he,hc.trans (Nat.mul_le_mul_right _ (by decide)),?_,zt,
    RationalAccumulator.blank_of_eq (ft.tapes 1249 (by decide)) privateBlank,ft.mono ?_⟩
  · intro j hj
    rw [←restoreSeed_values p round index v fields zero j hj]
    exact bt j hj
  · intro j hj
    simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    tauto

#print axioms restoreSeed_executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
