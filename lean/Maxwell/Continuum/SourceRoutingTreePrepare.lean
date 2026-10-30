import Maxwell.Continuum.SourceRoutingSourceArithmetic
import Maxwell.Continuum.SourceRoutingTreeLayout

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Prepare
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def instructions : List NatAssign.Instruction :=
  [.copy 709 801,.copy 711 802,.copy 716 803,.copy 717 804,
    .copy 801 807,.copy 802 808,.copy 802 810,.copy 801 811,.copy 802 812,
    .copy 804 806,.copy 801 818,.multiply 802 818,.add 818 806,.copy 806 800,
    .copy 801 809,.multiply 802 809,.literal 818 11,.multiply 818 809,.literal 819 2]
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values instructions v
def writes : Finset ℕ := {800,801,802,803,804,806,807,808,809,810,811,812,818,819}

theorem valid : ∀a∈instructions,a.Valid SourceArithmetic.ids := by
  simp [instructions,NatAssign.Instruction.Valid,SourceArithmetic.ids,SourceArithmetic.sourcePorts,
    Division.ids,Division.controls]

theorem output_heap (v : ℕ→ℕ) : output v 806=v 717+v 711*v 709 := by
  change v 711*v 709+v 717=v 717+v 711*v 709
  omega
theorem output_base (v : ℕ→ℕ) : output v 800=output v 806 := rfl
theorem output_stride (v : ℕ→ℕ) : output v 809=stride (v 709) (v 711) := by
  change 11*(v 711*v 709)=11*(v 709*v 711)
  ring
theorem output_count (v : ℕ→ℕ) : output v 801=v 709 := rfl
theorem output_width (v : ℕ→ℕ) : output v 802=v 711 := rfl
theorem output_forward (v : ℕ→ℕ) : output v 803=v 716 := rfl
theorem output_backward (v : ℕ→ℕ) : output v 804=v 717 := rfl
theorem output_rootCount (v : ℕ→ℕ) : output v 807=v 709 := rfl
theorem output_rootWidth (v : ℕ→ℕ) : output v 808=v 711 := rfl
theorem output_depth (v : ℕ→ℕ) : output v 810=v 711 := rfl
theorem output_currentCount (v : ℕ→ℕ) : output v 811=v 709 := rfl
theorem output_currentWidth (v : ℕ→ℕ) : output v 812=v 711 := rfl
theorem output_two (v : ℕ→ℕ) : output v 819=2 := rfl

theorem output_other (v : ℕ→ℕ) (i : ℕ) (hi : i∉writes) : output v i=v i := by
  simp only [writes,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  rcases hi with ⟨h0,h1,h2,h3,h4,h6,h7,h8,h9,h10,h11,h12,h18,h19⟩
  simp [output,instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    Function.update,h0,h1,h2,h3,h4,h6,h7,h8,h9,h10,h11,h12,h18,h19]

theorem words (v : ℕ→ℕ) (B : ℕ) (hB : 4 ≤ B)
    (hv : ∀i∈SourceArithmetic.ids,(v i).bits.length ≤ B) :
    ∀i∈SourceArithmetic.ids,(output v i).bits.length ≤ 2^19*(B+1) := by
  intro i hi
  have hh:=NatAssign.values_width_bound SourceArithmetic.ids instructions valid v B hv (by
    simp only [instructions,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [NatAssign.Instruction.literalWidth,show (11 : ℕ).bits.length=4 by decide,
      show (2 : ℕ).bits.length=2 by decide]
    all_goals omega) i hi
  exact (Nat.le_succ _).trans hh

theorem executes (v : ℕ→ℕ) (B : ℕ) (hB : 4 ≤ B)
    (hv : ∀i∈SourceArithmetic.ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank SourceArithmetic.ids v s.val) (hc : PrivateVisit.Clean s) :
    ∃steps t,Executes input tape (NatAssign.code instructions) steps s t ∧
      steps ≤ 3000*8^19*(B+2)^2 ∧ NatAssign.Bank SourceArithmetic.ids (output v) t.val ∧
      PrivateVisit.Clean t ∧ BinaryPrecision.Frame SourceArithmetic.work s.val t.val := by
  exact SourceArithmetic.stage instructions valid v B hv (by
    simp only [instructions,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [NatAssign.Instruction.literalWidth,show (11 : ℕ).bits.length=4 by decide,
      show (2 : ℕ).bits.length=2 by decide]
    all_goals omega) input tape s hs hc

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Prepare
