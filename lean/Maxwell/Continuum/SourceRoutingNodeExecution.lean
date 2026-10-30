import Maxwell.Continuum.SourceRoutingNodeCleanup
import Maxwell.Cost.SplitNode.Complexity

/-! A single fixed node operation allocates the split slabs, computes the
two child permutations, and reclaims its represented work words. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Node
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def extra : Finset ℕ := {87,94,95,97,120,121,126,127,128}
def code : Code := .seq RoutingAllocator.code (.seq SplitNode.code NodeCleanup.code)
def layout (v : ℕ→ℕ) : SplitNode.Layout :=
  RoutingAllocator.layout (v 190) (v 191) (v 192) (v 193) (v 194)

def cleanupBudget (v : ℕ→ℕ) (k : ℕ) : ℕ :=
  WordCleanup.wordBudget (NodeCleanup.entries (layout v) k
    (List.replicate (v 192) false) (List.replicate (v 192-1) false)
    (RoutingAllocator.outputValues v))

def costBound (v : ℕ→ℕ) (k B : ℕ) : ℕ :=
  3000*8^RoutingAllocator.statements.length*(B+2)^2+
    7000000*(2*2^k+1)*((2*2^k).bits.length+1)*(SplitNode.budget (layout v) k+1)^2+
    (41*(6*cleanupBudget v k+4)+1)

structure Ready (v : ℕ→ℕ) (clock : List Bool) (s : BitRAMState) : Prop where
  bank : NatAssign.Bank RoutingAllocator.ids v s
  workspace : DoublingInit.Workspace s
  clock : Word s 83 clock
  extra : ∀i∈extra,Blank s i

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i, i=4 ∨ 10 ≤ i → i≠37 → i∉NodeCleanup.banks → t.tapes i=s.tapes i

private theorem allocator_keep (i : ℕ) (hlo : 4 ≤ i)
    (hi : i∉RoutingAllocator.ids) : i∉RoutingAllocator.work := by
  have subset : RoutingAllocator.work⊆({0,1,2,3}:Finset ℕ)∪RoutingAllocator.ids := by decide
  intro hm
  rcases Finset.mem_union.mp (subset hm) with hsmall|hids
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hsmall
    omega
  · exact hi hids

private theorem allocator_workspace {s t : BitRAMState}
    (hs : DoublingInit.Workspace s) (ht : NatAssign.Scratch t)
    (hf : BinaryPrecision.Frame RoutingAllocator.work s t) : DoublingInit.Workspace t := by
  have keep (i : ℕ) (hi : 4 ≤ i) (hj : i∉RoutingAllocator.ids) := hf.tapes i (allocator_keep i hi hj)
  refine ⟨⟨⟨ht 0 (by omega),ht 1 (by omega),ht 2 (by omega),ht 3 (by omega),
    ?_,?_,?_,?_⟩,?_,?_⟩,?_⟩
  · exact RationalAccumulator.blank_of_eq (keep 5 (by omega) (by decide)) hs.1.1.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 6 (by omega) (by decide)) hs.1.1.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 8 (by omega) (by decide)) hs.1.1.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (keep 9 (by omega) (by decide)) hs.1.1.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (keep 7 (by omega) (by decide)) hs.1.2.1
  · intro i hi
    exact RationalAccumulator.blank_of_eq (keep i (by dsimp [DoublingPass.Private] at hi; omega)
      (by simp only [RoutingAllocator.ids,Finset.mem_insert,Finset.mem_singleton];
          dsimp [DoublingPass.Private] at hi; omega)) (hs.1.2.2 i hi)
  · exact RationalAccumulator.blank_of_eq (keep 37 (by omega) (by decide)) hs.2

private theorem cleanup_workspace {s t : BitRAMState}
    (hs : DoublingInit.Workspace s) (ht : ∀i∈NodeCleanup.banks,Blank t i)
    (hf : BinaryPrecision.Frame NodeCleanup.banks.toFinset s t) : DoublingInit.Workspace t := by
  refine ⟨⟨ChildPermutation.scratch_of_tapes (fun i hi => hf.tapes i ?_) hs.1.1,
    RationalAccumulator.blank_of_eq (hf.tapes 7 (by decide)) hs.1.2.1,?_⟩,
    RationalAccumulator.blank_of_eq (hf.tapes 37 (by decide)) hs.2⟩
  · simp only [NodeCleanup.banks,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    omega
  · intro i hi
    apply ht i
    simp only [NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false]
    dsimp [DoublingPass.Private] at hi
    omega

theorem executes (v : ℕ→ℕ) (k B : ℕ) (clock : List Bool)
    (hn : v 191=2*2^k) (hw : v 192=k+2) (hc : clock.length=v 192)
    (hv : ∀i∈RoutingAllocator.ids,(v i).bits.length≤B)
    (data : ChildPermutation.Data k) (hcolors : data.colors=BinarySplit.colors k data.target)
    (hsource : IncidenceEncoding.Separated (v 193) ((v 191)*(v 192)) (v 194) ((v 191)*(v 192)))
    (hforward : v 193+(v 191)*(v 192)≤v 190)
    (hbackward : v 194+(v 191)*(v 192)≤v 190)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready v clock s.val)
    (hf : BitArray.Represents s.val.memory (v 193) (v 192)
      (DoublingPass.words (v 192) (Vector.ofFn data.target)))
    (hb : BitArray.Represents s.val.memory (v 194) (v 192)
      (DoublingPass.words (v 192) (Vector.ofFn data.target.symm))) :
    ∃steps t, Executes input tape code steps s t ∧ steps≤costBound v k B ∧
      ChildPermutation.Represents ((layout v).child (2*2^k)) t.val.memory data
        (ChildPermutation.finalOutputs ((layout v).child (2*2^k)).childWidth data) ∧
      DoublingInit.Workspace t.val ∧ (∀i∈NodeCleanup.banks,Blank t.val i) ∧
      Frame s.val t.val ∧ SplitNode.MemoryFrame (layout v) k s.val.memory t.val.memory := by
  have scratch : NatAssign.Scratch s.val := by
    intro i hi
    interval_cases i
    · exact hs.workspace.1.1.1
    · exact hs.workspace.1.1.2.1
    · exact hs.workspace.1.1.2.2.1
    · exact hs.workspace.1.1.2.2.2.1
  obtain ⟨ac,a,ea,hac,ar,ab,az,af⟩ := RoutingAllocator.executes_bounded v clock B hv input tape s
    hs.bank scratch hs.clock
  have aextra (i : ℕ) (hi : i∈extra) : Blank a.val i := by
    apply RationalAccumulator.blank_of_eq (af.tapes i (allocator_keep i ?_ ?_)) (hs.extra i hi)
    all_goals simp only [extra,Finset.mem_insert,Finset.mem_singleton] at hi
    · omega
    · simp only [RoutingAllocator.ids,Finset.mem_insert,Finset.mem_singleton]; omega
  have separated : (layout v).split.Separated (2*2^k) := by
    simpa only [layout,hn] using RoutingAllocator.split_separated (v 190) (v 191) (v 192)
      (v 193) (v 194) hforward hbackward hsource
  have childSeparated : ((layout v).child (2*2^k)).Separated k := by
    simp only [layout,hn,hw]
    exact RoutingAllocator.child_separated _ _ _ _ (by simpa only [hn,hw] using hforward)
  obtain ⟨bc,b,childClock,hbc,eb,bcfg,blen,bwork,b126,brep,bcount,bsaved,bframe,bmem,
      broute,b94,b95,b97,bchild,b98,b99⟩ :=
    SplitNode.Reusable.executes k input tape (layout v) data clock hcolors hw hc separated childSeparated a
      (by simpa only [hn] using ar.count) (aextra 94 (by decide)) (aextra 95 (by decide))
      (aextra 97 (by decide)) ar.config ar.saved (allocator_workspace hs.workspace az af)
      (by simpa only [af.memory,layout,RoutingAllocator.layout] using hf)
      (by simpa only [af.memory,layout,RoutingAllocator.layout] using hb) ar.children
      (aextra 87 (by decide)) (aextra 120 (by decide)) (aextra 121 (by decide))
      (aextra 126 (by decide)) (aextra 127 (by decide)) (aextra 128 (by decide))
  have bheader : ∀i∈Finset.Icc 190 196,RationalAccumulator.Word b.val i (RoutingAllocator.outputValues v i) := by
    intro i hi
    have hilo := Finset.mem_Icc.mp hi
    apply RationalAccumulator.word_of_eq (bframe.2.2.2.1 i (by omega) ?_)
    · exact ab i (by simp only [RoutingAllocator.ids,Finset.mem_insert,Finset.mem_singleton]; omega)
    · simp only [SplitNode.Private,DoublingPass.RoundPrivate,DoublingPass.Private,ChildPermutation.MetadataPrivate]
      omega
  let bstate : NodeCleanup.State (layout v) k clock childClock (RoutingAllocator.outputValues v) b.val :=
    ⟨bcfg,broute,bsaved,bwork,b94,b95,b97,b126,bcount,bchild,b98,b99,bheader⟩
  obtain ⟨cc,t,ec,hcc,zt,cf⟩ := NodeCleanup.executes (layout v) k clock childClock
    (RoutingAllocator.outputValues v) input tape b bstate
  have cbudget : WordCleanup.wordBudget (NodeCleanup.entries (layout v) k clock childClock
      (RoutingAllocator.outputValues v))=cleanupBudget v k := by
    have hchild : childClock.length=v 192-1 := blen
    simp only [cleanupBudget,WordCleanup.wordBudget,NodeCleanup.entries,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,List.length_replicate,hc,hchild]
  have splitCost := SplitNode.costCap_bound (layout v) k clock hc
  refine ⟨ac+(bc+cc),t,ea.seq (eb.seq ec),?_,?_,cleanup_workspace bwork zt cf,zt,?_,?_⟩
  · rw [cbudget] at hcc
    dsimp only [costBound]
    omega
  · simpa only [cf.memory] using brep
  · refine ⟨cf.inputHead.trans (bframe.1.trans af.inputHead),
      cf.randomCursor.trans (bframe.2.1.trans af.randomCursor),
      cf.output.trans (bframe.2.2.1.trans af.output),?_⟩
    intro i hi h37 hout
    have hi' : i∉RoutingAllocator.ids := by
      intro hm
      have subset : RoutingAllocator.ids⊆NodeCleanup.banks.toFinset := by decide
      exact hout (List.mem_toFinset.mp (subset hm))
    refine (cf.tapes i (by simpa using hout)).trans
      ((bframe.2.2.2.1 i hi ?_).trans (af.tapes i (allocator_keep i (by omega) hi')))
    simp only [NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false,not_or] at hout
    simp only [SplitNode.Private,DoublingPass.RoundPrivate,DoublingPass.Private,ChildPermutation.MetadataPrivate]
    omega
  · intro p hp hj
    exact (congrFun cf.memory p).trans ((bmem p hp hj).trans (congrFun af.memory p))

#print axioms executes

end Maxwell.Cost.RoutingPorts.Complete.Tree.Node
