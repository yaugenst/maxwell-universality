import Maxwell.Continuum.SourceRoutingAssemblyAdvance

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyAdvance
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def writes : Finset ℕ := {811,812,813,814,815,816,817,818}

theorem output_other (v : ℕ→ℕ) (i : ℕ) (hi : i∉writes) : output v i=v i := by
  simp only [writes,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  rcases hi with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  simp [output,finish,first,second,Division.result,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update,h0,h1,h2,h3,h4,h5,h6,h7]

theorem output_count (v : ℕ→ℕ) : output v 811=v 819*v 811 := rfl
theorem output_width (v : ℕ→ℕ) : output v 812=v 812+1 := by
  dsimp [output,finish,first,second,Division.result,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  omega
theorem output_population (v : ℕ→ℕ) : output v 813=v 813/v 819 := rfl
theorem output_first (v : ℕ→ℕ) : output v 814=v 814/v 819 := rfl
theorem output_index (v : ℕ→ℕ) : output v 815=0 := rfl

theorem coordinates (v : ℕ→ℕ) (heap rootCount rootWidth d k j : ℕ)
    (hs : AssemblyCoordinates.Stored v heap rootCount rootWidth (d+1) k j) :
    AssemblyCoordinates.Stored (output v) heap rootCount rootWidth d (k+1) 0 := by
  refine ⟨(output_other v 806 (by decide)).trans hs.heap,
    (output_other v 809 (by decide)).trans hs.stride,?_,?_,?_,output_index v,
    (output_other v 819 (by decide)).trans hs.two⟩
  · rw [output_count,hs.two,hs.count,pow_succ']
  · rw [output_width,hs.width]
  · rw [output_first,hs.first,hs.two,pow_succ]
    have hp : 0<(2 : ℕ)^d := by positivity
    omega

theorem population (v : ℕ→ℕ) (d : ℕ) (hn : v 813=2^(d+1)) (htwo : v 819=2) :
    output v 813=2^d := by
  rw [output_population,hn,htwo,pow_succ]
  omega

theorem quotient_zero (v : ℕ→ℕ)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,output v i=0 := by
  intro i hi
  have disjoint : Disjoint Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts writes := by decide
  rw [output_other v i (Finset.disjoint_left.mp disjoint hi)]
  exact hz i hi

#print axioms coordinates
#print axioms population
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyAdvance
