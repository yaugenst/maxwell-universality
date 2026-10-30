import Maxwell.Continuum.SourceRoutingTreeArithmetic

/-! A non-root node's descriptor is computed from its breadth-first
coordinates. The parent number and branch are obtained by division by two. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Descriptor
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

-- 806: heap, 809: stride, 811: count, 812: width,
-- 814: first node minus one, 815: local index, 819: literal two.
def prepare : List NatAssign.Instruction := [.copy 814 805,.add 815 805]
def finish : List NatAssign.Instruction :=
  [.copy 805 800,.literal 818 1,.add 818 800,.multiply 809 800,.add 806 800,
   .copy 811 801,.copy 812 802,
   .copy 816 803,.multiply 809 803,.add 806 803,
   .copy 811 818,.multiply 819 818,
   .copy 812 804,.literal 816 1,.add 816 804,.multiply 804 818,
   .copy 817 816,.multiply 819 816,.literal 804 6,.add 804 816,
   .multiply 818 816,.add 816 803,.copy 803 804,.add 818 804]

def divided (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (Function.update (NatAssign.values prepare v) 816 ((v 814+v 815)/2))
    817 ((v 814+v 815)%2)
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finish (divided v)
def code : Code := .seq (NatAssign.code prepare)
  (.seq (Division.code 805 819 816 817) (NatAssign.code finish))

theorem prepare_valid : ∀a∈prepare,a.Valid Division.ids := by
  simp [prepare,NatAssign.Instruction.Valid,Division.ids,Division.controls]
theorem finish_valid : ∀a∈finish,a.Valid Division.ids := by
  simp [finish,NatAssign.Instruction.Valid,Division.ids,Division.controls]

theorem prepare_value (v : ℕ→ℕ) : NatAssign.values prepare v 805=v 814+v 815 := by
  dsimp [prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  omega

theorem prepare_other (v : ℕ→ℕ) (i : ℕ) (hi : i≠805) :
    NatAssign.values prepare v i=v i := by
  simp [prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update,hi]

theorem divided_eq (v : ℕ→ℕ) (htwo : v 819=2) :
    Function.update (Function.update (NatAssign.values prepare v) 816
        (NatAssign.values prepare v 805/NatAssign.values prepare v 819)) 817
        (NatAssign.values prepare v 805%NatAssign.values prepare v 819)=divided v := by
  rw [prepare_value,prepare_other v 819 (by decide),htwo]
  rfl

theorem output_heap (v : ℕ→ℕ) : output v 800=v 806+(v 814+v 815+1)*v 809 := by
  dsimp [output,divided,prepare,finish,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  ring
theorem output_count (v : ℕ→ℕ) : output v 801=v 811 := by rfl
theorem output_width (v : ℕ→ℕ) : output v 802=v 812 := by rfl
theorem output_forward (v : ℕ→ℕ) (htwo : v 819=2) :
    output v 803=v 806+((v 814+v 815)/2)*v 809+
      (6+2*((v 814+v 815)%2))*((2*v 811)*(v 812+1)) := by
  dsimp [output,divided,prepare,finish,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  rw [htwo]
  ring
theorem output_backward (v : ℕ→ℕ) (htwo : v 819=2) :
    output v 804=v 806+((v 814+v 815)/2)*v 809+
      (7+2*((v 814+v 815)%2))*((2*v 811)*(v 812+1)) := by
  dsimp [output,divided,prepare,finish,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  rw [htwo]
  ring

theorem persistent (v : ℕ→ℕ) (i : ℕ) (hi : i∈Finset.Icc 806 815 ∨ i=819) : output v i=v i := by
  have hi' : i≠800 ∧ i≠801 ∧ i≠802 ∧ i≠803 ∧ i≠804 ∧ i≠805 ∧ i≠816 ∧ i≠817 ∧ i≠818 := by
    simp only [Finset.mem_Icc] at hi
    omega
  rcases hi' with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  simp [output,divided,prepare,finish,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update,h0,h1,h2,h3,h4,h5,h6,h7,h8]

#print axioms output_forward
#print axioms output_backward
end Maxwell.Cost.RoutingPorts.Complete.Tree.Descriptor
