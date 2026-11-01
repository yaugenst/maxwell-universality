import Maxwell.Continuum.SourceRoutingSourceColors
import Maxwell.Continuum.SourceRoutingPhaseStartupPlan
import Maxwell.Cost.ArrayReindex

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePhase
open Maxwell.Logical Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

abbrev half (S : Source.SparseSystem) (p : ℕ) : ℕ := portHalfSide (SourcePlan.indexedVertices S p)
abbrev side (S : Source.SparseSystem) (p : ℕ) : ℕ := 2*half S p
theorem half_pos (S : Source.SparseSystem) (p : ℕ) : 0<half S p := by unfold half portHalfSide;positivity
theorem side_pos (S : Source.SparseSystem) (p : ℕ) : 0<side S p := by unfold side;exact Nat.mul_pos (by decide) (half_pos S p)
theorem square (S : Source.SparseSystem) (p : ℕ) : side S p*side S p=SourcePlan.size S p :=
  SourcePlan.indexed_size S p

def layout (S : Source.SparseSystem) (p : ℕ) : Layout (side S p*side S p) where
  forward := (SourcePlan.treeLayout S p).forward
  backward := (SourcePlan.treeLayout S p).backward
  clock := (SourcePlan.treeLayout S p).clock
  positive := Nat.mul_pos (side_pos S p) (side_pos S p)
  clock_length := by
    rw [square,SourcePlan.source_width]
    simpa only [Tree.CompleteTree.count_width] using (SourcePlan.treeLayout S p).clock_length
  separated := by
    rw [square,SourcePlan.source_width,←SourcePlan.tree_count]
    simpa only [Tree.CompleteTree.count_width] using (SourcePlan.treeLayout S p).separated

theorem ordered (S : Source.SparseSystem) (p : ℕ) :
    (layout S p).forward+side S p*side S p*(side S p*side S p).bits.length≤(layout S p).backward := by
  change (SourcePlan.treeLayout S p).forward+side S p*side S p*(side S p*side S p).bits.length≤
    (SourcePlan.treeLayout S p).backward
  rw [square,SourcePlan.source_width,←SourcePlan.tree_count]
  exact (SourcePlan.forward_end S p).le

def plan (S : Source.SparseSystem) (p : ℕ) : GeometryPhase.Plan (side S p) :=
  PhaseStartup.plan (side S p) (side_pos S p) (layout S p) (ordered S p)

theorem sequential (S : Source.SparseSystem) (p : ℕ) : GeometryHistories.Sequential (plan S p) :=
  PhaseStartup.sequential _ _ _ _

theorem labels_base (S : Source.SparseSystem) (p : ℕ) : (plan S p).base 1=SourcePlan.labelBase S p := by
  change (SourcePlan.treeLayout S p).backward+11*(side S p*side S p*(side S p*side S p).bits.length)=_
  rw [square]
  unfold SourcePlan.labelBase Tree.TreeStartup.heap
  simp only [SourcePlan.tree_count,←SourcePlan.source_width]
  ring

theorem metadata (S : Source.SparseSystem) (p : ℕ) (s : BitRAMState)
    (hs : Metadata (Startup.gridLayout (SourcePlan.vertices S p) (SourceGraph.Positive.base S p)) s) :
    Metadata (layout S p) s := by
  refine ⟨?_,?_,hs.forward,hs.backward,hs.clock⟩
  · simpa only [square,SourcePlan.size] using hs.count
  · simpa only [square,SourcePlan.size] using hs.width

#print axioms labels_base

end Maxwell.Cost.RoutingPorts.Complete.SourcePhase
