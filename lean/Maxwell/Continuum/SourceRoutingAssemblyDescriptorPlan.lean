import Maxwell.Continuum.SourceRoutingTreeArithmetic
import Maxwell.Continuum.SourceRoutingTreeColorAddress

/-! The reverse-pass descriptor uses stored child count and width.  Its
single division selects the color slab by the runtime width parity. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyDescriptor
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def divided (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (Function.update v 816 (v 812/v 819)) 817 (v 812%v 819)
def finish : List NatAssign.Instruction :=
  [.copy 811 801,.multiply 819 801,.copy 812 802,.literal 818 1,.add 818 802,
   .copy 814 800,.add 815 800,
   .copy 800 803,.multiply 819 803,.add 818 803,
   .copy 803 804,.add 818 804,
   .multiply 809 800,.add 806 800,
   .multiply 809 803,.add 806 803,.multiply 809 804,.add 806 804,
   .copy 811 816,.multiply 812 816,.literal 818 10,.multiply 818 816,
   .add 816 803,.add 816 804,
   .copy 801 816,.multiply 802 816,
   .multiply 819 817,.literal 818 2,.add 818 817,
   .copy 800 805,.multiply 816 817,.add 817 805,
   .literal 818 10,.multiply 818 816,.add 816 800]
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finish (divided v)
def code : Code := .seq (Division.code 812 819 816 817) (NatAssign.code finish)

theorem finish_valid : ∀a∈finish,a.Valid Division.ids := by
  simp [finish,NatAssign.Instruction.Valid,Division.ids,Division.controls]

theorem output_count (v : ℕ→ℕ) : output v 801=v 819*v 811 := rfl
theorem output_width (v : ℕ→ℕ) : output v 802=v 812+1 := by
  dsimp [output,finish,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  omega

theorem output_parent (v : ℕ→ℕ) (htwo : v 819=2) :
    output v 800=v 806+(v 814+v 815)*v 809+10*((2*v 811)*(v 812+1)) := by
  dsimp [output,finish,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  rw [htwo]
  ring
theorem output_left (v : ℕ→ℕ) (htwo : v 819=2) :
    output v 803=v 806+(2*(v 814+v 815)+1)*v 809+10*(v 811*v 812) := by
  dsimp [output,finish,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  rw [htwo]
  ring
theorem output_right (v : ℕ→ℕ) (htwo : v 819=2) :
    output v 804=v 806+(2*(v 814+v 815)+2)*v 809+10*(v 811*v 812) := by
  dsimp [output,finish,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  rw [htwo]
  ring
theorem output_colors (v : ℕ→ℕ) (htwo : v 819=2) :
    output v 805=v 806+(v 814+v 815)*v 809+
      ColorAddress.slot (v 812+1)*((2*v 811)*(v 812+1)) := by
  dsimp [output,finish,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,Function.update]
  rw [htwo]
  have parity : (v 812+1+1)%2=v 812%2 := by omega
  simp only [ColorAddress.slot,parity]
  ring

def writes : Finset ℕ := {800,801,802,803,804,805,816,817,818}
theorem output_other (v : ℕ→ℕ) (i : ℕ) (hi : i∉writes) : output v i=v i := by
  simp only [writes,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  rcases hi with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  simp [output,finish,divided,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update,h0,h1,h2,h3,h4,h5,h6,h7,h8]

#print axioms output_colors
#print axioms output_other
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyDescriptor
