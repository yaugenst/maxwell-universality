import Maxwell.Continuum.SourceRoutingTreeStorage
import Maxwell.Continuum.SourceRoutingTreeOutputs

/-! Stored node outputs provide both exact logical child permutations.
The statement does not require retaining a redundant parent-input witness. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Outputs
open Maxwell.Logical.Routing Coloring Coloring.NumericSplit
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem child_forward (rows columns : ℕ) (target : Targets.Target rows (columns+1))
    (layout : SplitNode.Layout) (memory : ℕ→Bool)
    (h : Stored layout (columns+rows) (ColorData.splitData rows columns target) memory) (b : Bool) :
    Storage.Permutation rows columns (ColorData.childTarget rows columns target b) memory
      ((layout.child (2*2^(columns+rows))).outputBase ⟨2*b.toNat,by cases b <;> decide⟩)
      (layout.child (2*2^(columns+rows))).childWidth := by
  apply (Storage.numeric _ _ _ _ _ _).mpr
  cases b
  · have hh:=h.children 0
    rw [Storage.final_words,ChildPermutation.Data.finalPerm_zero,ColorData.splitData_left] at hh
    exact hh
  · have hh:=h.children 2
    rw [Storage.final_words,ChildPermutation.Data.finalPerm_two,ColorData.splitData_right] at hh
    exact hh

theorem child_backward (rows columns : ℕ) (target : Targets.Target rows (columns+1))
    (layout : SplitNode.Layout) (memory : ℕ→Bool)
    (h : Stored layout (columns+rows) (ColorData.splitData rows columns target) memory) (b : Bool) :
    Storage.Permutation rows columns (ColorData.childTarget rows columns target b).symm memory
      ((layout.child (2*2^(columns+rows))).outputBase ⟨2*b.toNat+1,by cases b <;> decide⟩)
      (layout.child (2*2^(columns+rows))).childWidth := by
  apply (Storage.numeric _ _ _ _ _ _).mpr
  cases b
  · have hh:=h.children 1
    rw [Storage.final_words,ChildPermutation.Data.finalPerm_one,ColorData.splitData_left,←Storage.inverse_numeric] at hh
    exact hh
  · have hh:=h.children 3
    rw [Storage.final_words,ChildPermutation.Data.finalPerm_three,ColorData.splitData_right,←Storage.inverse_numeric] at hh
    exact hh

def At (heap rootCount rootWidth node rows columns : ℕ)
    (target : Targets.Target rows (columns+1)) (memory : ℕ→Bool) : Prop :=
  Stored (RoutingAllocator.layout (block heap rootCount rootWidth node)
    (2*2^(columns+rows)) (columns+rows+2) 0 0) (columns+rows)
    (ColorData.splitData rows columns target) memory

theorem at_iff (heap rootCount rootWidth node rows columns forward backward : ℕ)
    (target : Targets.Target rows (columns+1)) (memory : ℕ→Bool) :
    Stored (RoutingAllocator.layout (block heap rootCount rootWidth node)
      (2*2^(columns+rows)) (columns+rows+2) forward backward) (columns+rows)
      (ColorData.splitData rows columns target) memory ↔
      At heap rootCount rootWidth node rows columns target memory := by
  constructor
  · intro h;exact ⟨h.colors,h.children⟩
  · intro h;exact ⟨h.colors,h.children⟩

theorem At.children {heap rootCount rootWidth node rows columns : ℕ}
    {target : Targets.Target rows (columns+1)} {memory : ℕ→Bool}
    (h : At heap rootCount rootWidth node rows columns target memory) (b : Bool) :
    Storage.Permutation rows columns (ColorData.childTarget rows columns target b) memory
      (RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^(columns+rows))
        (columns+rows+2) (6+2*b.toNat)) (columns+rows+1) ∧
    Storage.Permutation rows columns (ColorData.childTarget rows columns target b).symm memory
      (RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^(columns+rows))
        (columns+rows+2) (7+2*b.toNat)) (columns+rows+1) := by
  have hf:=child_forward rows columns target _ memory h b
  have hb:=child_backward rows columns target _ memory h b
  rw [SplitNode.Layout.child_outputBase] at hf hb
  have hw : columns+rows+2-1=columns+rows+1 := by omega
  change Storage.Permutation rows columns (ColorData.childTarget rows columns target b) memory
    (RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^(columns+rows))
      (columns+rows+2) (6+2*b.toNat)) (columns+rows+2-1) at hf
  change Storage.Permutation rows columns (ColorData.childTarget rows columns target b).symm memory
    (RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^(columns+rows))
      (columns+rows+2) (6+(2*b.toNat+1))) (columns+rows+2-1) at hb
  rw [hw] at hf hb
  exact ⟨hf,by simpa only [show 6+(2*b.toNat+1)=7+2*b.toNat by omega] using hb⟩

#print axioms At.children
end Maxwell.Cost.RoutingPorts.Complete.Tree.Outputs
