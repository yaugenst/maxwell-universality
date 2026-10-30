import Maxwell.Continuum.SourceRoutingSourceTree
import Maxwell.Continuum.SourceRoutingIndexedColor

/-! The fixed source-driven tree program returns exactly the numeric colors
used by the declared continuum geometry. -/

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Maxwell.Logical.Routing
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def labelBase (S : Source.SparseSystem) (p : ℕ) : ℕ :=
  Tree.TreeStartup.heap (depth S p) (treeLayout S p).backward+
    10*(size S p*(size S p).bits.length)

def colorValues (S : Source.SparseSystem) (p : ℕ) : Vector ℕ (size S p) :=
  Vector.ofFn (fun i => 2^depth S p*
    ((Composition.SourceRouting.indexedData S p).colors.color ((indexedPortIndex S p).symm i)).val)

theorem labels_colors (S : Source.SparseSystem) (p : ℕ) (memory : ℕ→Bool)
    (hs : Tree.LabelsAt (Tree.TreeStartup.heap (depth S p) (treeLayout S p).backward)
      (Tree.TreeStartup.count (depth S p)) (Tree.TreeStartup.wordWidth (depth S p))
      0 (depth S p) (depth S p) (root S p) memory) :
    BitArray.Represents memory (labelBase S p) (size S p).bits.length
      (IncidenceEncoding.words (size S p).bits.length (colorValues S p)) := by
  refine ⟨fun i => ?_,?_⟩
  · change (((colorValues S p).map (IncidenceEncoding.word (size S p).bits.length)).get i).length=_
    rw [Tree.Storage.map_get]
    simp [IncidenceEncoding.word]
  intro i j hj
  let a:=(ports S p).symm ((indexedPortIndex S p).symm i)
  have hi : (Tree.ColorData.index (depth S p) (depth S p) a).val=i.val := by
    have h:=congrArg (fun e => e a) (ports_index S p)
    simpa [a,Equiv.trans_apply] using congrArg Fin.val h
  have hw : depth S p+depth S p+1=(size S p).bits.length := (source_width S p).symm
  have hb : Tree.Leaves.labelBase (Tree.TreeStartup.heap (depth S p) (treeLayout S p).backward)
      (Tree.TreeStartup.count (depth S p)) (Tree.TreeStartup.wordWidth (depth S p)) 0
      (2^(depth S p+depth S p)) (depth S p+depth S p+1)=labelBase S p := by
    simp only [Tree.Leaves.labelBase,Tree.block,RoutingAllocator.slab,Nat.zero_mul,Nat.add_zero,
      tree_power,hw,labelBase]
  have h:=hs a j (by omega)
  dsimp only at h
  simp only [hw] at hb
  simp only [root_label,hi,hw,hb] at h
  simpa [IncidenceEncoding.words,colorValues,Vector.get,Fin.cast,a,IncidenceEncoding.word] using h

#print axioms labels_colors
end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
