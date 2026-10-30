import Maxwell.Continuum.SourceRoutingPrivateZeroHandoff
import Maxwell.Continuum.SourceRoutingTreeArithmetic

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Allocation
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def prepare : List NatAssign.Instruction := [.copy 813 801,.multiply 819 801]
def prepared (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values prepare v
def decreased (v : ℕ→ℕ) : ℕ→ℕ := Function.update (prepared v) 801 (prepared v 801-1)
def finish : List NatAssign.Instruction := [.multiply 809 801]
def zeroValues (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values finish (decreased v)
def restore : List NatAssign.Instruction := [.copy 807 801,.literal 813 2]
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values restore (zeroValues v)
def length (v : ℕ→ℕ) : ℕ := v 809*(v 819*v 813-1)

theorem prepare_valid : ∀a∈prepare,a.Valid Division.ids := by
  simp [prepare,NatAssign.Instruction.Valid,Division.ids,Division.controls]
theorem finish_valid : ∀a∈finish,a.Valid Division.ids := by
  simp [finish,NatAssign.Instruction.Valid,Division.ids,Division.controls]
theorem restore_valid : ∀a∈restore,a.Valid Division.ids := by
  simp [restore,NatAssign.Instruction.Valid,Division.ids,Division.controls]

theorem prepared_width (v : ℕ→ℕ) (B : ℕ) (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(prepared v i).bits.length ≤ 4*(B+1) := by
  intro i hi
  exact (Nat.le_succ _).trans (NatAssign.values_width_bound Division.ids prepare prepare_valid v B hv
    (by simp [prepare,NatAssign.Instruction.literalWidth]) i hi)

theorem decreased_width (v : ℕ→ℕ) (B : ℕ) (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(decreased v i).bits.length ≤ 4*(B+1) := by
  intro i hi
  by_cases he : i=801
  · subst i
    exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le (prepared v 801) 1)).trans
      (prepared_width v B hv 801 (by decide))
  · simpa only [decreased,Function.update_of_ne he] using prepared_width v B hv i hi

theorem zero_width (v : ℕ→ℕ) (B : ℕ) (hv : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    ∀i∈Division.ids,(zeroValues v i).bits.length ≤ 16*(B+1) := by
  intro i hi
  have hh:=NatAssign.values_width_bound Division.ids finish finish_valid (decreased v) (4*(B+1))
    (decreased_width v B hv) (by simp [finish,NatAssign.Instruction.literalWidth]) i hi
  change (zeroValues v i).bits.length+1 ≤ 2*(4*(B+1)+1) at hh
  omega

theorem zero_base (v : ℕ→ℕ) : zeroValues v 800=v 800 := rfl
theorem zero_length (v : ℕ→ℕ) : zeroValues v 801=length v := rfl
theorem output_count (v : ℕ→ℕ) : output v 801=v 807 := rfl
theorem output_population (v : ℕ→ℕ) : output v 813=2 := rfl
theorem output_other (v : ℕ→ℕ) (i : ℕ) (h801 : i≠801) (h813 : i≠813) : output v i=v i := by
  simp [output,restore,zeroValues,finish,decreased,prepared,prepare,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,Function.update,h801,h813]

#print axioms zero_width
end Maxwell.Cost.RoutingPorts.Complete.Tree.Allocation
