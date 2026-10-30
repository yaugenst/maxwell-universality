import Maxwell.Continuum.SourceRoutingTreeMemory
import Maxwell.Continuum.SourceRoutingNodeWordBounds

/-! Each node retains its split colors and four child permutations inside
its own block; later visits to disjoint blocks preserve these outputs. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Outputs
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

structure Stored (layout : SplitNode.Layout) (k : ℕ) (data : ChildPermutation.Data k)
    (memory : ℕ→Bool) : Prop where
  colors : BitArray.Represents memory (layout.child (2*2^k)).colors 1 (ColorPass.colorWords data.colors)
  children : ∀i,BitArray.Represents memory ((layout.child (2*2^k)).outputBase i)
    (layout.child (2*2^k)).childWidth
    (ChildPermutation.finalOutputs (layout.child (2*2^k)).childWidth data i)

theorem of_represents {layout : SplitNode.Layout} {k : ℕ} {data : ChildPermutation.Data k}
    {memory : ℕ→Bool}
    (h : ChildPermutation.Represents (layout.child (2*2^k)) memory data
      (ChildPermutation.finalOutputs (layout.child (2*2^k)).childWidth data)) : Stored layout k data memory :=
  ⟨h.colors,h.outputs⟩

theorem colors_bounds (heap rootCount rootWidth node k forward backward : ℕ)
    (hn : 2*2^k ≤ rootCount) (hw : k+2 ≤ rootWidth) :
    let layout:=RoutingAllocator.layout (block heap rootCount rootWidth node) (2*2^k) (k+2) forward backward
    block heap rootCount rootWidth node ≤ (layout.child (2*2^k)).colors ∧
      (layout.child (2*2^k)).colors+2*2^k ≤ block heap rootCount rootWidth node+stride rootCount rootWidth := by
  dsimp only
  have hs (j : ℕ) (hj : j<11) := slab_fits heap rootCount rootWidth node (2*2^k) (k+2) j hn hw hj
  have hsize : 2*2^k ≤ (2*2^k)*(k+2) := Nat.le_mul_of_pos_right _ (by omega)
  have he := NodeWords.after_eq
    (RoutingAllocator.layout (block heap rootCount rootWidth node) (2*2^k) (k+2) forward backward).split.route
    (2*2^k).bits.length
  dsimp only [SplitNode.Layout.child,BinarySplit.finalLayout,CycleSplit.colorLayout]
  rcases he with he|he
  all_goals rw [he]
  all_goals dsimp only [RoutingAllocator.layout,DoublingPass.Layout.flip]
  · have hh:=hs 4 (by omega); exact ⟨hh.1,by omega⟩
  · have hh:=hs 2 (by omega); exact ⟨hh.1,by omega⟩

theorem children_bounds (heap rootCount rootWidth node k forward backward : ℕ)
    (hn : 2*2^k ≤ rootCount) (hw : k+2 ≤ rootWidth) (i : Fin 4) :
    let layout:=RoutingAllocator.layout (block heap rootCount rootWidth node) (2*2^k) (k+2) forward backward
    block heap rootCount rootWidth node ≤ (layout.child (2*2^k)).outputBase i ∧
      (layout.child (2*2^k)).outputBase i+2^k*(layout.child (2*2^k)).childWidth ≤
        block heap rootCount rootWidth node+stride rootCount rootWidth := by
  dsimp only
  rw [SplitNode.Layout.child_outputBase]
  change _ ≤ RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) (6+i.val) ∧
    RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) (6+i.val)+2^k*(k+2-1) ≤ _
  have hh:=slab_fits heap rootCount rootWidth node (2*2^k) (k+2) (6+i.val) hn hw (by omega)
  have hsize : 2^k*(k+2-1) ≤ (2*2^k)*(k+2) := Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
  exact ⟨hh.1,by omega⟩

theorem preserve (heap rootCount rootWidth a b k forward backward : ℕ) (hab : a≠b)
    (hn : 2*2^k ≤ rootCount) (hw : k+2 ≤ rootWidth) (data : ChildPermutation.Data k)
    (before after : ℕ→Bool)
    (hf : Memory.Frame (block heap rootCount rootWidth b) (stride rootCount rootWidth) before after)
    (hs : Stored (RoutingAllocator.layout (block heap rootCount rootWidth a) (2*2^k) (k+2) forward backward)
      k data before) :
    Stored (RoutingAllocator.layout (block heap rootCount rootWidth a) (2*2^k) (k+2) forward backward) k data after := by
  constructor
  · have hh:=colors_bounds heap rootCount rootWidth a k forward backward hn hw
    exact hf.represents (Memory.other_block heap rootCount rootWidth a b _ _ _ hab hh.1
      (by simpa only [Nat.mul_one] using hh.2)) hs.colors
  · intro i
    have hh:=children_bounds heap rootCount rootWidth a k forward backward hn hw i
    exact hf.represents (Memory.other_block heap rootCount rootWidth a b _ _ _ hab hh.1 hh.2) (hs.children i)

#print axioms preserve
end Maxwell.Cost.RoutingPorts.Complete.Tree.Outputs
