import Maxwell.Continuum.SourceRoutingLevelPlan

/-! Closed forms for the controller words prevent word-width bounds from
growing by induction through the sequence of visited nodes. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def writes : Finset ℕ := {800,801,802,803,804,805,815,816,817,818}

theorem output_other (v : ℕ→ℕ) (j : ℕ) (hj : j∉writes) : Step.output v j=v j := by
  simp only [writes,Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  rcases hj with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  simp [Step.output,Step.increment,Descriptor.output,Descriptor.divided,Descriptor.prepare,
    Descriptor.finish,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    Function.update,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem output_index (v : ℕ→ℕ) : Step.output v 815=v 815+1 := by
  dsimp [Step.output,Step.increment,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  rw [Descriptor.persistent v 815 (by simp)]
  omega

theorem values_other (v : ℕ→ℕ) (i j : ℕ) (hj : j∉writes) : values v i j=v j := by
  induction i with
  | zero => rfl
  | succ i ih => rw [←values_next,output_other _ _ hj,ih]

theorem values_index (v : ℕ→ℕ) (i : ℕ) : values v i 815=v 815+i := by
  induction i with
  | zero => simp [values]
  | succ i ih => rw [←values_next,output_index,ih];omega

def basis (v : ℕ→ℕ) (i : ℕ) : ℕ→ℕ := Function.update v 815 (v 815+i)

theorem output_twice (v : ℕ→ℕ) : Step.output (Step.output v)=Step.output (basis v 1) := by
  funext j
  by_cases hj : j∈writes
  · simp only [writes,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [basis,Step.output,Step.increment,Descriptor.output,Descriptor.divided,Descriptor.prepare,
      Descriptor.finish,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,Function.update,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  · rw [output_other _ _ hj,output_other _ _ hj,output_other _ _ hj]
    have h815 : j≠815 := by intro he;subst j;exact hj (by decide)
    simp [basis,Function.update,h815]

theorem basis_twice (v : ℕ→ℕ) (i : ℕ) : basis (basis v i) 1=basis v (i+1) := by
  funext j
  by_cases hj : j=815
  · subst j;simp [basis];omega
  · simp [basis,Function.update,hj]

theorem values_successor (v : ℕ→ℕ) (i : ℕ) : values v (i+1)=Step.output (basis v i) := by
  induction i with
  | zero =>
      have hb : basis v 0=v := by funext j;simp [basis]
      rw [hb]
      exact (values_next v 0).symm
  | succ i ih => rw [←values_next,ih,output_twice,basis_twice]

#print axioms values_successor
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
