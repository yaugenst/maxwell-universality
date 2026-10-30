import Maxwell.Continuum.SourceRoutingAssemblyDescriptor
import Maxwell.Continuum.SourceRoutingAssemblyGeometry

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyCoordinates
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

structure Stored (v : ℕ→ℕ) (heap rootCount rootWidth d k j : ℕ) : Prop where
  heap : v 806=heap
  stride : v 809=Tree.stride rootCount rootWidth
  count : v 811=2^k
  width : v 812=k+1
  first : v 814=2^d-1
  index : v 815=j
  two : v 819=2

theorem descriptor_layout (v : ℕ→ℕ) (heap rootCount rootWidth d k : ℕ) (i : Fin (2^d))
    (hs : Stored v heap rootCount rootWidth d k i.val) :
    Assembly.layout (AssemblyDescriptor.output v)=AssemblyNode.layout heap rootCount rootWidth (levelNode d i) k := by
  have hp:=AssemblyDescriptor.output_parent v hs.two
  have hl:=AssemblyDescriptor.output_left v hs.two
  have hr:=AssemblyDescriptor.output_right v hs.two
  have hc:=AssemblyDescriptor.output_colors v hs.two
  have hw:=AssemblyDescriptor.output_width v
  simp only [hs.heap,hs.stride,hs.count,hs.width,hs.first,hs.index] at hp hl hr hc hw
  have width : k+1+1=k+2 := by omega
  rw [width] at hp hc hw
  dsimp only [Assembly.layout,AssemblyNode.layout]
  rw [hw,hp,hc,hl,hr]
  simp [Leaves.labelBase,RoutingAllocator.slab,block,levelNode,child,Nat.add_assoc]

theorem count (v : ℕ→ℕ) (heap rootCount rootWidth d k j : ℕ)
    (hs : Stored v heap rootCount rootWidth d k j) : AssemblyDescriptor.output v 801=2*2^k := by
  rw [AssemblyDescriptor.output_count,hs.two,hs.count]

#print axioms descriptor_layout
end Maxwell.Cost.RoutingPorts.Complete.Tree.AssemblyCoordinates
