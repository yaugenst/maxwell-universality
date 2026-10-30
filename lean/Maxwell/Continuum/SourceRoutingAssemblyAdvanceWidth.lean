import Maxwell.Continuum.SourceRoutingAssemblyAdvanceValues
import Maxwell.Continuum.SourceRoutingAssemblyWidths

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyAdvance
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

theorem output_dependency (v : ℕ→ℕ) (i : ℕ) (hi : i∈writes) :
    output v i=output (ControllerWidth.restricted v) i := by
  simp only [writes,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [output,finish,first,second,Division.result,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.value,NatAssign.Instruction.target,
    Function.update,ControllerWidth.restricted,ControllerWidth.reads]

theorem words (v : ℕ→ℕ) (L T : ℕ) (hL : 1 ≤ L)
    (hv : ∀i∈ControllerWidth.reads,(v i).bits.length ≤ L)
    (ht : ∀i∈Division.ids,(v i).bits.length ≤ T)
    (hT : AssemblyLevel.uniformWidth L ≤ T) :
    ∀i∈Division.ids,(output v i).bits.length ≤ T := by
  have wr:=ControllerWidth.restricted_width v L hv
  have w1:=Division.result_width (ControllerWidth.restricted v) 813 819 813 816 L (by decide) wr
  have w2:=Division.result_width (first (ControllerWidth.restricted v)) 814 819 814 817 L (by decide) w1
  have lit : ∀a∈finish,a.literalWidth ≤ L := by
    simp [finish,NatAssign.Instruction.literalWidth];exact hL
  intro i hi
  by_cases written : i∈writes
  · rw [output_dependency _ _ written]
    have hh:=NatAssign.values_width_bound Division.ids finish finish_valid
      (second (ControllerWidth.restricted v)) L w2 lit i hi
    change (output (ControllerWidth.restricted v) i).bits.length+1 ≤ 16*(L+1) at hh
    have small : 16*(L+1) ≤ AssemblyLevel.uniformWidth L := by
      dsimp only [AssemblyLevel.uniformWidth];omega
    omega
  · rw [output_other _ _ written]
    exact ht i hi

#print axioms words
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyAdvance
