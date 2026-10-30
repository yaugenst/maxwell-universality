import Maxwell.Continuum.SourceRoutingTreePrepare
import Maxwell.Continuum.SourceRoutingTreeDepth
import Maxwell.Continuum.SourceRoutingTreePower
import Maxwell.Continuum.SourceRoutingTreeAllocation
import Maxwell.Continuum.SourceRoutingRootRun

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.TreeStartup
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def count (total : ℕ) : ℕ := 2^(total+total)
def wordWidth (total : ℕ) : ℕ := total+total+1
def heap (total backward : ℕ) : ℕ := backward+wordWidth total*count total
def seed (total forward backward : ℕ) : ℕ→ℕ := SourceArithmetic.seed (count total) (wordWidth total) forward backward
def selected (total forward backward : ℕ) : ℕ→ℕ := Depth.output (Prepare.output (seed total forward backward))
def powered (total forward backward : ℕ) : ℕ→ℕ :=
  Function.update (selected total forward backward) 813 (2^(selected total forward backward 810))
def output (total forward backward : ℕ) : ℕ→ℕ := Allocation.output (powered total forward backward)
def bits (total forward backward : ℕ) : ℕ :=
  (count total).bits.length+(wordWidth total).bits.length+forward.bits.length+backward.bits.length+4
def stageBits (total forward backward : ℕ) : ℕ := 2^19*(bits total forward backward+1)

theorem seed_words (total forward backward : ℕ) :
    ∀i∈SourceArithmetic.ids,(seed total forward backward i).bits.length ≤ bits total forward backward := by
  intro i _
  simp only [seed,SourceArithmetic.seed]
  split_ifs <;> simp only [bits,show (0 : ℕ).bits.length=0 by decide] <;> omega

theorem selected_depth (total forward backward : ℕ) : selected total forward backward 810=total := by
  apply Depth.output_depth
  · rw [Prepare.output_depth]
    change wordWidth total=2*total+1
    dsimp only [wordWidth];omega
  · exact Prepare.output_two _

theorem selected_other (total forward backward i : ℕ) (h810 : i≠810) (h816 : i≠816) :
    selected total forward backward i=Prepare.output (seed total forward backward) i :=
  Depth.output_other _ i h810 h816

theorem prepared_zero (total forward backward : ℕ) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Prepare.output (seed total forward backward) i=0 := by
  intro i hi
  have disjoint : Disjoint Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts Prepare.writes := by decide
  rw [Prepare.output_other _ _ (Finset.disjoint_left.mp disjoint hi)]
  simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> rfl

theorem selected_words (total forward backward : ℕ) :
    ∀i∈Division.ids,(selected total forward backward i).bits.length ≤ stageBits total forward backward := by
  apply Depth.output_width
  intro i hi
  exact Prepare.words _ (bits total forward backward) (by dsimp only [bits];omega)
    (seed_words total forward backward) i (Finset.mem_union_left _ hi)

theorem powered_words (total forward backward : ℕ) :
    ∀i∈Division.ids,(powered total forward backward i).bits.length ≤ stageBits total forward backward := by
  intro i hi
  by_cases he : i=813
  · subst i
    rw [powered,Function.update_self,selected_depth]
    have smaller:=Maxwell.Continuum.RationalWords.bits_mono
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show total ≤ total+total by omega))
    change (2^total).bits.length ≤ stageBits total forward backward
    have hb : (count total).bits.length ≤ bits total forward backward := by dsimp only [bits];omega
    have widen : bits total forward backward ≤ stageBits total forward backward := by
      dsimp only [stageBits];omega
    exact smaller.trans (hb.trans widen)
  · simpa only [powered,Function.update_of_ne he] using selected_words total forward backward i hi

theorem powered_zero (total forward backward : ℕ) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,powered total forward backward i=0 := by
  intro i hi
  have hn : i≠813 := by
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  rw [powered,Function.update_of_ne hn]
  exact Depth.output_zero _ (prepared_zero total forward backward) i hi

theorem output_words_raw (total forward backward : ℕ) :
    ∀i∈Division.ids,(output total forward backward i).bits.length ≤ 4*(16*(stageBits total forward backward+1)+1) := by
  intro i hi
  exact (Nat.le_succ _).trans (NatAssign.values_width_bound Division.ids Allocation.restore Allocation.restore_valid
    (Allocation.zeroValues (powered total forward backward)) (16*(stageBits total forward backward+1))
    (Allocation.zero_width _ _ (powered_words total forward backward)) (by
      simp [Allocation.restore,NatAssign.Instruction.literalWidth,show (2 : ℕ).bits.length=2 by decide]
      omega) i hi)

theorem output_other (total forward backward i : ℕ) (h801 : i≠801) (h810 : i≠810)
    (h813 : i≠813) (h816 : i≠816) :
    output total forward backward i=Prepare.output (seed total forward backward) i := by
  rw [output,Allocation.output_other _ _ h801 h813,powered,Function.update_of_ne h813,
    selected_other _ _ _ _ h810 h816]

theorem output_depth (total forward backward : ℕ) : output total forward backward 810=total := by
  rw [output,Allocation.output_other _ _ (by decide) (by decide),powered,
    Function.update_of_ne (by decide : (810 : ℕ)≠813),selected_depth]

theorem allocation_length (total forward backward : ℕ) :
    Allocation.length (powered total forward backward)=(2^(total+1)-1)*stride (count total) (wordWidth total) := by
  simp only [Allocation.length,powered,Function.update_self,
    Function.update_of_ne (by decide : (809 : ℕ)≠813),Function.update_of_ne (by decide : (819 : ℕ)≠813),
    selected_depth,selected_other _ _ _ 809 (by decide) (by decide),
    selected_other _ _ _ 819 (by decide) (by decide),Prepare.output_stride,Prepare.output_two]
  change stride (count total) (wordWidth total)*(2*2^total-1)=_
  rw [pow_succ']
  exact Nat.mul_comm _ _

#print axioms powered_words
#print axioms allocation_length
end Maxwell.Cost.RoutingPorts.Complete.Tree.TreeStartup
