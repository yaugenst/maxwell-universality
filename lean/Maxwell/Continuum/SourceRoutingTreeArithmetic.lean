import Maxwell.Continuum.SourceRoutingTreeDivision
import Maxwell.Continuum.NatAssignOutputWidth
import Maxwell.Cost.PhysicalMaterial.FixedSubtract

/-! Charged fixed arithmetic stages for the routing-tree controls. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Arithmetic
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def work : Finset ℕ := {0,1,2,3}∪Division.ids
theorem work_subset : work⊆Division.work := by
  intro i hi
  simp only [work,Division.work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
  tauto

theorem stage (instructions : List NatAssign.Instruction)
    (hv : ∀a∈instructions,a.Valid Division.ids)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈Division.ids,(v i).bits.length ≤ B)
    (hl : ∀a∈instructions,a.literalWidth ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) :
    ∃steps t, Executes input tape (NatAssign.code instructions) steps s t ∧
      steps ≤ 3000*8^instructions.length*(B+2)^2 ∧
      NatAssign.Bank Division.ids (NatAssign.values instructions v) t.val ∧
      PrivateVisit.Clean t ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,t,he,hcost,bt,zt,ft⟩ := NatAssign.executes Division.ids
    (fun i hi => by have:=Division.ids_lower i hi;omega) instructions hv v input tape s hs (Workspace.scratch hc)
  have subset : NatAssign.changes instructions⊆work := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · apply Finset.mem_union_left
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢
      tauto
    · obtain ⟨a,ha,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
      have ht : a.target∈Division.ids := by
        have hh:=hv a ha
        cases a <;> simp only [NatAssign.Instruction.Valid,NatAssign.Instruction.target] at hh ⊢
        · exact hh
        · exact hh.2.1
        · exact hh.2.1
        · exact hh.2.1
      exact Finset.mem_union_right _ (he ▸ ht)
  have frame := ft.mono subset
  exact ⟨steps,t,he,hcost.trans (NatAssign.price_bound Division.ids instructions hv v B hw hl),
    bt,Workspace.of_frame hc zt (frame.mono work_subset) Division.work_disjoint,frame⟩

theorem decrement (target : ℕ) (ht : target∈Division.controls) (v : ℕ→ℕ)
    (hpos : 0<v target) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) :
    ∃steps t, Executes input tape (PhysicalMaterial.FixedSubtract.code target 1) steps s t ∧
      steps ≤ 29*(v target).bits.length+31 ∧
      NatAssign.Bank Division.ids (Function.update v target (v target-1)) t.val ∧
      PrivateVisit.Clean t ∧ BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨steps,t,he,hcost,wt,ft⟩ := PhysicalMaterial.FixedSubtract.executes target 1 (v target)
    (by omega) input tape s (hs target (Finset.mem_union_left _ ht))
  have bt : NatAssign.Bank Division.ids (Function.update v target (v target-1)) t.val := by
    intro i hi
    by_cases hit : i=target
    · subst i; simpa only [Function.update_self] using wt
    · simpa only [Function.update_of_ne hit] using RationalAccumulator.word_of_eq
        (ft.tapes i (by simpa using hit)) (hs i hi)
  have htarget : target∈Division.work := Finset.mem_union_right _ (Finset.mem_union_left _ ht)
  have zt : NatAssign.Scratch t.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (ft.tapes i ?_) (Workspace.scratch hc i hi)
    have hlo:=Division.ids_lower target (Finset.mem_union_left _ ht)
    simp only [Finset.mem_singleton]
    omega
  refine ⟨steps,t,he,?_,bt,Workspace.of_frame hc zt ft ?_,ft⟩
  · dsimp only [PhysicalMaterial.FixedSubtract.costBound] at hcost
    omega
  · intro i hi hlo
    have hkeep:=Division.work_disjoint i hi hlo
    simp only [Finset.mem_singleton]
    intro he
    exact hkeep (he ▸ htarget)

#print axioms stage
#print axioms decrement
end Maxwell.Cost.RoutingPorts.Complete.Tree.Arithmetic
