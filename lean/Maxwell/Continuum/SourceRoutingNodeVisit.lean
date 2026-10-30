import Maxwell.Continuum.SourceRoutingNodeSetup
import Maxwell.Continuum.SourceRoutingNodeRelocation

/-! A reusable fixed tree-node visit starts from five stored coordinates
and blank work tapes, and returns the exact two child permutations. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.NodeVisit
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def code : Code := .seq NodeSetup.code Node.code
def bound (q : ℕ→ℕ) (k B : ℕ) : ℕ :=
  NodeSetup.bound B+Node.costBound (NodeSetup.descriptor q) k B
def Clean (s : BitRAMState) : Prop := DoublingInit.Workspace s ∧ ∀i∈NodeCleanup.banks,Blank s i
def Inputs (q : ℕ→ℕ) (s : BitRAMState) : Prop :=
  ∀i∈NodeSetup.controls,RationalAccumulator.Word s i (q i)

theorem initial_bank (q : ℕ→ℕ) (s : BitRAMState) (hc : Clean s) (hi : Inputs q s) :
    NatAssign.Bank NodeSetup.ids (NodeSetup.initial q) s := by
  intro i hids
  by_cases hin : i∈NodeSetup.controls
  · simpa [NodeSetup.initial,hin] using hi i hin
  · have hid : i∈RoutingAllocator.ids := (Finset.mem_union.mp hids).resolve_left hin
    have sub : RoutingAllocator.ids⊆NodeCleanup.banks.toFinset := by decide
    have zero := (RationalAccumulator.zero_word_iff_blank s i).mpr (hc.2 i (List.mem_toFinset.mp (sub hid)))
    simpa [NodeSetup.initial,hin] using zero

theorem descriptor_width (q : ℕ→ℕ) (B : ℕ) (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B) :
    ∀i∈RoutingAllocator.ids,(NodeSetup.descriptor q i).bits.length ≤ B := by
  intro i _
  simp only [NodeSetup.descriptor]
  split_ifs
  · exact hq 800 (by decide)
  · exact hq 801 (by decide)
  · exact hq 802 (by decide)
  · exact hq 803 (by decide)
  · exact hq 804 (by decide)
  · simp

theorem executes (q : ℕ→ℕ) (k B : ℕ) (hn : q 801=2*2^k) (hw : q 802=k+2)
    (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B)
    (data : ChildPermutation.Data k) (hcolors : data.colors=BinarySplit.colors k data.target)
    (hsource : IncidenceEncoding.Separated (q 803) ((q 801)*(q 802)) (q 804) ((q 801)*(q 802)))
    (hforward : q 803+(q 801)*(q 802) ≤ q 800)
    (hbackward : q 804+(q 801)*(q 802) ≤ q 800)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Clean s.val) (hin : Inputs q s.val)
    (hf : BitArray.Represents s.val.memory (q 803) (q 802)
      (DoublingPass.words (q 802) (Vector.ofFn data.target)))
    (hb : BitArray.Represents s.val.memory (q 804) (q 802)
      (DoublingPass.words (q 802) (Vector.ofFn data.target.symm))) :
    ∃steps t, Executes input tape code steps s t ∧ steps ≤ bound q k B ∧
      ChildPermutation.Represents ((Node.layout (NodeSetup.descriptor q)).child (2*2^k)) t.val.memory data
        (ChildPermutation.finalOutputs ((Node.layout (NodeSetup.descriptor q)).child (2*2^k)).childWidth data) ∧
      Clean t.val ∧ Inputs q t.val ∧ Node.Frame s.val t.val ∧
      SplitNode.MemoryFrame (Node.layout (NodeSetup.descriptor q)) k s.val.memory t.val.memory := by
  obtain ⟨ac,a,ea,hac,ar,af⟩ := NodeSetup.executes q B hq input tape s (initial_bank q s.val hs hin) hs.1
    (hs.2 83 (by decide)) (fun i hi => hs.2 i (by
      have subset : Node.extra⊆NodeCleanup.banks.toFinset := by decide
      exact List.mem_toFinset.mp (subset hi)))
  obtain ⟨bc,t,eb,hbc,rep,work,zero,bf,bm⟩ := Node.executes (NodeSetup.descriptor q) k B (q 801).bits
    (by simpa [NodeSetup.descriptor] using hn) (by simpa [NodeSetup.descriptor] using hw)
    (by simpa [NodeSetup.descriptor,hw] using NodeSetup.clock_length q k hn)
    (descriptor_width q B hq) data hcolors
    (by simpa [NodeSetup.descriptor] using hsource)
    (by simpa [NodeSetup.descriptor] using hforward)
    (by simpa [NodeSetup.descriptor] using hbackward) input tape a ar
    (by simpa [NodeSetup.descriptor,af.memory] using hf)
    (by simpa [NodeSetup.descriptor,af.memory] using hb)
  have frame : Node.Frame s.val t.val := by
    refine ⟨bf.inputHead.trans af.inputHead,bf.randomCursor.trans af.randomCursor,
      bf.output.trans af.output,?_⟩
    intro i hi h37 hout
    refine (bf.tapes i hi h37 hout).trans (af.tapes i ?_)
    have subset : NodeSetup.work⊆({0,1,2,3}:Finset ℕ)∪NodeCleanup.banks.toFinset := by decide
    intro hm
    rcases Finset.mem_union.mp (subset hm) with hsmall|hbank
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hsmall
      omega
    · exact hout (List.mem_toFinset.mp hbank)
  refine ⟨ac+bc,t,ea.seq eb,Nat.add_le_add hac hbc,rep,⟨work,zero⟩,?_,frame,?_⟩
  · intro i hi
    apply RationalAccumulator.word_of_eq (frame.tapes i ?_ ?_ ?_) (hin i hi)
    all_goals simp only [NodeSetup.controls,Finset.mem_insert,Finset.mem_singleton] at hi
    · omega
    · omega
    · rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  · intro p hp hj
    exact (bm p hp hj).trans (congrFun af.memory p)

#print axioms executes

end Maxwell.Cost.RoutingPorts.Complete.Tree.NodeVisit
