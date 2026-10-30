import Maxwell.Continuum.SourceRoutingLevelAdvance
import Maxwell.Continuum.SourceRoutingTreeCoordinates

/-! The runtime next-level arithmetic agrees with the binary tree's exact
count, width, population, first node and reset local index. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level.Advance
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def writes : Finset ℕ := {811,812,813,814,815,816}

theorem output_other (v : ℕ→ℕ) (i : ℕ) (hi : i∉writes) : output v i=v i := by
  simp only [writes,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  rcases hi with ⟨h0,h1,h2,h3,h4,h5⟩
  simp [output,instructions,decreased,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update,h0,h1,h2,h3,h4,h5]

theorem output_count (v : ℕ→ℕ) : output v 811=v 811/v 819 := rfl
theorem output_width (v : ℕ→ℕ) : output v 812=v 812-1 := rfl
theorem output_nodes (v : ℕ→ℕ) : output v 813=v 819*v 813 := rfl
theorem output_first (v : ℕ→ℕ) : output v 814=v 819*(v 814+1) := by
  dsimp [output,instructions,decreased,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update]
  ring
theorem output_index (v : ℕ→ℕ) : output v 815=0 := rfl

theorem coordinates (v : ℕ→ℕ) (heap rootCount rootWidth d n w j : ℕ) (hd : 1 ≤ d)
    (hs : Coordinates.Stored v heap rootCount rootWidth d n w j) :
    Coordinates.Stored (output v) heap rootCount rootWidth (d+1) (n/2) (w-1) 0 := by
  refine ⟨?_,?_,?_,?_,?_,output_index v,?_⟩
  · exact (output_other v 806 (by decide)).trans hs.heap
  · exact (output_other v 809 (by decide)).trans hs.stride
  · rw [output_count,hs.count,hs.two]
  · rw [output_width,hs.width]
  · rw [output_first,hs.two,hs.first,pow_succ]
    have hp : 2 ≤ (2 : ℕ)^d := by exact Nat.le_self_pow (by omega) 2
    omega
  · exact (output_other v 819 (by decide)).trans hs.two

theorem quotient_zero (v : ℕ→ℕ)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,output v i=0 := by
  intro i hi
  rw [output_other v i]
  · exact hz i hi
  · have h : Disjoint Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts writes := by decide
    exact Finset.disjoint_left.mp h hi

#print axioms coordinates
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level.Advance
