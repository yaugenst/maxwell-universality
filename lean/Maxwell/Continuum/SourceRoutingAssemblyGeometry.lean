import Maxwell.Continuum.SourceRoutingLeafLabels
import Maxwell.Continuum.SourceRoutingTreeColorAddress
import Maxwell.Continuum.SourceRoutingPrivateAssembly

/-! The reverse pass reads its two children's label slabs and the actual
split colors.  Their separation follows from the allocated tree geometry. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyNode
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def layout (heap rootCount rootWidth node k : ℕ) : ChildPermutation.Layout :=
  ⟨k+2,Leaves.labelBase heap rootCount rootWidth node (2*2^k) (k+2),
    RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) (ColorAddress.slot (k+2)),
    Leaves.labelBase heap rootCount rootWidth (child node false) (2^k) (k+1),0,
    Leaves.labelBase heap rootCount rootWidth (child node true) (2^k) (k+1),0⟩

theorem separated (heap rootCount rootWidth node k : ℕ)
    (hn : 2*2^k ≤ rootCount) (hw : k+2 ≤ rootWidth) :
    ColorAssemble.Separated (layout heap rootCount rootWidth node k) k := by
  have hsmall : 2^k ≤ rootCount := by omega
  have hwidth : k+1 ≤ rootWidth := by omega
  have childSep (b : Bool) := slab_separated heap rootCount rootWidth (child node b) node
    (2^k) (k+1) (2*2^k) (k+2) 10 10 (by dsimp only [child];omega)
    hsmall hwidth hn hw (by omega) (by omega)
  refine ⟨?_,?_,?_⟩
  · have cb:=ColorAddress.bounds (k+2)
    have hh:=RoutingAllocator.slab_separated (block heap rootCount rootWidth node)
      (2*2^k) (k+2) (ColorAddress.slot (k+2)) 10 (by omega)
    have size : 2*2^k ≤ (2*2^k)*(k+2) := Nat.le_mul_of_pos_right _ (by omega)
    change IncidenceEncoding.Separated _ (2*2^k) _ ((2*2^k)*(k+2))
    dsimp only [layout,Leaves.labelBase]
    rcases hh with hh|hh
    · exact Or.inl (by omega)
    · exact Or.inr hh
  · simpa only [layout,Leaves.labelBase,ChildPermutation.Layout.childWidth,
      show k+2-1=k+1 by omega] using childSep false
  · simpa only [layout,Leaves.labelBase,ChildPermutation.Layout.childWidth,
      show k+2-1=k+1 by omega] using childSep true

theorem memory_frame (heap rootCount rootWidth node k : ℕ)
    (hn : 2*2^k ≤ rootCount) (hw : k+2 ≤ rootWidth)
    (before after : ℕ→Bool)
    (hf : ColorAssemble.MemoryFrame (layout heap rootCount rootWidth node k) k before after) :
    Memory.Frame (block heap rootCount rootWidth node) (stride rootCount rootWidth) before after := by
  intro p hp
  apply hf p
  have hh:=slab_fits heap rootCount rootWidth node (2*2^k) (k+2) 10 hn hw (by omega)
  change p<RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) 10 ∨
    RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) 10+(2*2^k)*(k+2) ≤ p
  rcases hp with hp|hp
  · exact Or.inl (hp.trans_le hh.1)
  · exact Or.inr (hh.2.trans hp)

#print axioms separated
#print axioms memory_frame
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyNode
