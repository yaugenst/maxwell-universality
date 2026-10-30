import Maxwell.Continuum.SourceRoutingRawWorkspace
import Maxwell.Cost.PositiveGraph.Initialize.Fill

/-! One actual one-bit fill initializes the entire bounded routing heap.
This also supplies the zero leaf labels without assuming untouched memory. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.ZeroHeap
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def controls : Finset ℕ := {800,801}
def banks : Finset ℕ := {140,141,142,160,161,162}
def ids : Finset ℕ := controls∪banks
def initial (q : ℕ→ℕ) (i : ℕ) : ℕ := if i∈controls then q i else 0
def setup : List NatAssign.Instruction := [.literal 140 1,.copy 800 141,.copy 801 142]
def output (q : ℕ→ℕ) : ℕ→ℕ := NatAssign.values setup (initial q)
def ports : PositiveGraph.Initialize.Ports := ⟨140,141,140,142,by simp⟩

theorem setup_executes (q : ℕ→ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hq : ∀i∈controls,(q i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NodeVisit.Clean s.val) (hb : ∀i∈banks,Blank s.val i)
    (hi : ∀i∈controls,RationalAccumulator.Word s.val i (q i)) :
    ∃steps t,Executes input tape (NatAssign.code setup) steps s t ∧ steps ≤ 2^24*(B+2)^2 ∧
      NatAssign.Bank ids (output q) t.val ∧ NodeVisit.Clean t.val ∧
      BinaryPrecision.Frame (NatAssign.changes setup) s.val t.val := by
  have valid : ∀a∈setup,a.Valid ids := by simp [setup,NatAssign.Instruction.Valid,ids,controls,banks]
  have lower : ∀i∈ids,4 ≤ i := by
    intro i hi
    simp only [ids,controls,banks,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  have bank : NatAssign.Bank ids (initial q) s.val := by
    intro i hi'
    by_cases hc : i∈controls
    · simpa [initial,hc] using hi i hc
    · have hh:=(Finset.mem_union.mp hi').resolve_left hc
      simpa [initial,hc] using (RationalAccumulator.zero_word_iff_blank _ _).mpr (hb i hh)
  have scratch : NatAssign.Scratch s.val := by
    intro i hi'
    exact (Workspace.raw_iff s.val).mp hs i (Finset.mem_union_left _ (by
      simp only [Workspace.small,Finset.mem_insert,Finset.mem_singleton];omega))
  have width : ∀i∈ids,(initial q i).bits.length ≤ B := by
    intro i _
    by_cases hc : i∈controls
    · simpa [initial,hc] using hq i hc
    · simp [initial,hc]
  have literal : ∀a∈setup,a.literalWidth ≤ B := by simp [setup,NatAssign.Instruction.literalWidth];omega
  obtain ⟨steps,t,he,hcost,bt,zt,ft⟩:=NatAssign.executes ids lower setup valid (initial q) input tape s bank scratch
  have clean:=Workspace.raw_of_frame hs zt ft (by
    intro i hi' hlo
    have hd : Disjoint (Workspace.raw\({0,1,2,3}:Finset ℕ)) (NatAssign.changes setup) := by decide
    apply Finset.disjoint_left.mp hd
    exact Finset.mem_sdiff.mpr ⟨hi',by simp only [Finset.mem_insert,Finset.mem_singleton];omega⟩)
  refine ⟨steps,t,he,?_,bt,clean,ft⟩
  have price:=NatAssign.price_bound ids setup valid (initial q) B width literal
  change NatAssign.price setup (initial q) ≤ 3000*8^3*(B+2)^2 at price
  exact hcost.trans (price.trans (Nat.mul_le_mul_right _ (by norm_num)))

#print axioms setup_executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.ZeroHeap
