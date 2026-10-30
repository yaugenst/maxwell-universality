import Maxwell.Continuum.SourceRoutingAssemblyStep
import Maxwell.Continuum.SourceRoutingLevelValues

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def values (v : ℕ→ℕ) (i : ℕ) : ℕ→ℕ := (AssemblyStep.output^[i]) v
def writes : Finset ℕ := {800,801,802,803,804,805,815,816,817,818}

theorem values_next (v : ℕ→ℕ) (i : ℕ) : AssemblyStep.output (values v i)=values v (i+1) :=
  (Function.iterate_succ_apply' _ _ _).symm

theorem output_other (v : ℕ→ℕ) (i : ℕ) (hi : i∉writes) : AssemblyStep.output v i=v i := by
  simp only [writes,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  rcases hi with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  simp [AssemblyStep.output,Step.increment,AssemblyDescriptor.output,AssemblyDescriptor.divided,
    AssemblyDescriptor.finish,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    Function.update,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem output_index (v : ℕ→ℕ) : AssemblyStep.output v 815=v 815+1 := by
  dsimp [AssemblyStep.output,Step.increment,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  rw [AssemblyDescriptor.output_other v 815 (by decide)]
  omega

theorem values_other (v : ℕ→ℕ) (n i : ℕ) (hi : i∉writes) : values v n i=v i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [←values_next,output_other _ _ hi,ih]

theorem values_index (v : ℕ→ℕ) (n : ℕ) : values v n 815=v 815+n := by
  induction n with
  | zero => simp [values]
  | succ n ih => rw [←values_next,output_index,ih];omega

theorem output_twice (v : ℕ→ℕ) : AssemblyStep.output (AssemblyStep.output v)=AssemblyStep.output (Level.basis v 1) := by
  funext i
  by_cases hi : i∈writes
  · simp only [writes,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [Level.basis,AssemblyStep.output,Step.increment,AssemblyDescriptor.output,AssemblyDescriptor.divided,
      AssemblyDescriptor.finish,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,Function.update,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  · rw [output_other _ _ hi,output_other _ _ hi,output_other _ _ hi]
    have h815 : i≠815 := by intro he;subst i;exact hi (by decide)
    simp [Level.basis,Function.update,h815]

theorem values_successor (v : ℕ→ℕ) (n : ℕ) : values v (n+1)=AssemblyStep.output (Level.basis v n) := by
  induction n with
  | zero =>
      have hb : Level.basis v 0=v := by funext i;simp [Level.basis]
      rw [hb]
      exact (values_next v 0).symm
  | succ n ih => rw [←values_next,ih,output_twice,Level.basis_twice]

theorem coordinates (v : ℕ→ℕ) (heap rootCount rootWidth d k : ℕ)
    (hs : AssemblyCoordinates.Stored v heap rootCount rootWidth d k 0) (i : ℕ) :
    AssemblyCoordinates.Stored (values v i) heap rootCount rootWidth d k i := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (values_other v i 806 (by decide)).trans hs.heap
  · exact (values_other v i 809 (by decide)).trans hs.stride
  · exact (values_other v i 811 (by decide)).trans hs.count
  · exact (values_other v i 812 (by decide)).trans hs.width
  · exact (values_other v i 814 (by decide)).trans hs.first
  · rw [values_index,hs.index];omega
  · exact (values_other v i 819 (by decide)).trans hs.two

#print axioms values_successor
#print axioms coordinates
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyLevel
