import Maxwell.Continuum.SourceRoutingSourceTreeLayout

/-! One source-driven program computes the routing permutation, allocates
the whole routing tree, executes both traversals, and stores the exact
recursive root labels. No represented tree or per-level execution is an input. -/

namespace Maxwell.Cost.RoutingPorts.Complete.SourceTree
open Structured SourceGraph.Positive Maxwell.Logical.Routing
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def code : Code := .seq SourcePlan.code Tree.CompleteTree.code
def work : Finset ℕ := SourcePlan.work∪Tree.CompleteTree.work
def cost (S : Source.SparseSystem) (p : ℕ) (room : dimension S p<2^width S p) : ℕ :=
  SourcePlan.cost S p room+Tree.CompleteTree.cost (SourcePlan.depth S p)
    (SourcePlan.treeLayout S p).forward (SourcePlan.treeLayout S p).backward

theorem executes (S : Source.SparseSystem) (p : ℕ) (hm : 2 ≤ S.nnz)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : SourceGraph.Incidence.Result S p s) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost S p hs.room ∧
      Tree.LabelsAt (Tree.TreeStartup.heap (SourcePlan.depth S p) (SourcePlan.treeLayout S p).backward)
        (Tree.TreeStartup.count (SourcePlan.depth S p)) (Tree.TreeStartup.wordWidth (SourcePlan.depth S p))
        0 (SourcePlan.depth S p) (SourcePlan.depth S p) (SourcePlan.root S p) t.val.memory ∧
      Tree.PrivateVisit.Clean t ∧ Blank t.val 839 ∧ Blank t.val 831 ∧ Blank t.val 830 ∧
      ArchiveFrame work s.val t.val ∧
      Metadata (Startup.gridLayout (SourcePlan.vertices S p) (base S p)) t.val ∧
      (∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Blank t.val i) ∧
      Stored (Startup.gridLayout (SourcePlan.vertices S p) (base S p))
        ((DummyFill.scatter (DummyFill.pairs (SourcePlan.source S p) (SourcePlan.target S p))).map Fin.val)
        ((DummyFill.scatter ((DummyFill.pairs (SourcePlan.source S p) (SourcePlan.target S p)).map Prod.swap)).map Fin.val) t.val ∧
      (∀address,address<(SourcePlan.treeLayout S p).forward→t.val.memory address=s.val.memory address) := by
  obtain ⟨c0,a,e0,h0,ra,metadata,stored,oa,fa,qa⟩:=SourcePlan.executes_workspace S p hm input tape s hs
  obtain ⟨c1,t,e1,h1,labels,zt,t839,t831,t830,quotientClean,metadataT,mt,ft⟩:=Tree.CompleteTree.executes (SourcePlan.depth S p)
    (by dsimp only [SourcePlan.depth];omega) (SourcePlan.treeLayout S p) (SourcePlan.root S p)
    (SourcePlan.forward_bound S p) input tape a (SourcePlan.tree_metadata S p a.val metadata)
    (SourcePlan.private_ready hs ra fa) (SourcePlan.zero_ready hs fa)
    (SourcePlan.division_fresh hs fa qa)
    (SourcePlan.fresh_after hs fa 839 (by decide)) (SourcePlan.fresh_after hs fa 831 (by decide))
    (SourcePlan.fresh_after hs fa 830 (by decide))
    (SourcePlan.forward_stored S p a.val stored) (SourcePlan.backward_stored S p a.val stored)
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,labels,zt,t839,t831,t830,
    (fa.mono Finset.subset_union_left).trans (ft.mono Finset.subset_union_right),?_,quotientClean,?_,?_⟩
  · refine ⟨?_,?_,metadataT.forward,metadataT.backward,metadataT.clock⟩
    · simpa only [SourcePlan.tree_count,SourcePlan.size] using metadataT.count
    · simpa only [SourcePlan.tree_count,SourcePlan.size] using metadataT.width
  · have forwardEnd : (Startup.gridLayout (SourcePlan.vertices S p) (base S p)).forward+
        SourcePlan.size S p*(SourcePlan.size S p).bits.length ≤
        Tree.TreeStartup.heap (SourcePlan.depth S p) (SourcePlan.treeLayout S p).backward := by
      simpa only [SourcePlan.tree_count,←SourcePlan.source_width,SourcePlan.treeLayout]
        using SourcePlan.forward_bound S p
    have backwardEnd : (Startup.gridLayout (SourcePlan.vertices S p) (base S p)).backward+
        SourcePlan.size S p*(SourcePlan.size S p).bits.length =
        Tree.TreeStartup.heap (SourcePlan.depth S p) (SourcePlan.treeLayout S p).backward := by
      simp only [Tree.TreeStartup.heap,SourcePlan.tree_count,←SourcePlan.source_width,
        SourcePlan.treeLayout,Nat.mul_comm]
    exact ⟨mt.represents (Or.inl forwardEnd) stored.forward,
      mt.represents (Or.inl (Nat.le_of_eq backwardEnd)) stored.backward⟩
  intro address ha
  have endpoint:=SourcePlan.forward_bound S p
  have beforeHeap : address<Tree.TreeStartup.heap (SourcePlan.depth S p) (SourcePlan.treeLayout S p).backward := by
    exact lt_of_lt_of_le ha ((Nat.le_add_right _ _).trans endpoint)
  have beforeBackward : address<(SourcePlan.treeLayout S p).backward := by
    rw [←SourcePlan.forward_end]
    exact lt_of_lt_of_le ha (Nat.le_add_right _ _)
  exact (mt address (Or.inl beforeHeap)).trans (oa address (Or.inl ha) (Or.inl beforeBackward))

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.SourceTree
