import Maxwell.Continuum.SourceRoutingSourceTarget

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open SourceGraph.Positive
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def treeLayout (S : Source.SparseSystem) (p : ℕ) : Layout (Tree.TreeStartup.count (depth S p)) where
  forward := (Startup.gridLayout (vertices S p) (base S p)).forward
  backward := (Startup.gridLayout (vertices S p) (base S p)).backward
  clock := (Startup.gridLayout (vertices S p) (base S p)).clock
  positive := by dsimp only [Tree.TreeStartup.count];positivity
  clock_length := by
    simpa only [tree_count,size] using (Startup.gridLayout (vertices S p) (base S p)).clock_length
  separated := by
    simpa only [tree_count,size] using (Startup.gridLayout (vertices S p) (base S p)).separated

theorem tree_metadata (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState)
    (hs : Metadata (Startup.gridLayout (vertices S p) (base S p)) s) : Metadata (treeLayout S p) s := by
  refine ⟨?_,?_,hs.forward,hs.backward,hs.clock⟩
  · simpa only [tree_count,size] using hs.count
  · simpa only [tree_count,size] using hs.width

theorem source_width (S : Source.SparseSystem) (p : ℕ) :
    (size S p).bits.length=Tree.TreeStartup.wordWidth (depth S p) := by
  rw [←tree_count,Tree.CompleteTree.count_width]

theorem forward_end (S : Source.SparseSystem) (p : ℕ) :
    (treeLayout S p).forward+Tree.TreeStartup.count (depth S p)*Tree.TreeStartup.wordWidth (depth S p)=
      (treeLayout S p).backward := by
  change (base S p+4*vertices S p)+Tree.TreeStartup.count (depth S p)*Tree.TreeStartup.wordWidth (depth S p)=
    (base S p+4*vertices S p)+size S p*(size S p).bits.length
  rw [tree_count,source_width]

theorem forward_bound (S : Source.SparseSystem) (p : ℕ) :
    (treeLayout S p).forward+Tree.TreeStartup.count (depth S p)*Tree.TreeStartup.wordWidth (depth S p) ≤
      Tree.TreeStartup.heap (depth S p) (treeLayout S p).backward := by
  rw [forward_end]
  exact Nat.le_add_right _ _

#print axioms tree_metadata
#print axioms forward_bound
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
