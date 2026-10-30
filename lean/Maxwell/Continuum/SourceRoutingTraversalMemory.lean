import Maxwell.Continuum.SourceRoutingTreeChildren
import Maxwell.Continuum.SourceRoutingLevelCoordinates
import Maxwell.Continuum.SourceRoutingLeafLabels

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Outputs
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem preserve_before (heap rootCount rootWidth node first count k forward backward : ℕ)
    (hnode : node<first) (hn : 2*2^k ≤ rootCount) (hw : k+2 ≤ rootWidth)
    (data : ChildPermutation.Data k) (before after : ℕ→Bool)
    (hf : Memory.Frame (block heap rootCount rootWidth first) (count*stride rootCount rootWidth) before after)
    (hs : Stored (RoutingAllocator.layout (block heap rootCount rootWidth node)
      (2*2^k) (k+2) forward backward) k data before) :
    Stored (RoutingAllocator.layout (block heap rootCount rootWidth node)
      (2*2^k) (k+2) forward backward) k data after := by
  have boundary:=Level.block_before heap rootCount rootWidth node first hnode
  constructor
  · have cb:=colors_bounds heap rootCount rootWidth node k forward backward hn hw
    apply hf.represents (Or.inl ?_) hs.colors
    simpa only [Nat.mul_one] using cb.2.trans boundary
  · intro i
    have ib:=children_bounds heap rootCount rootWidth node k forward backward hn hw i
    exact hf.represents (Or.inl (ib.2.trans boundary)) (hs.children i)

theorem At.preserve_before {heap rootCount rootWidth node first count rows columns : ℕ}
    {target : Targets.Target rows (columns+1)} {before after : ℕ→Bool}
    (hnode : node<first) (hn : 2*2^(columns+rows) ≤ rootCount) (hw : columns+rows+2 ≤ rootWidth)
    (hf : Memory.Frame (block heap rootCount rootWidth first) (count*stride rootCount rootWidth) before after)
    (hs : At heap rootCount rootWidth node rows columns target before) :
    At heap rootCount rootWidth node rows columns target after :=
  Outputs.preserve_before heap rootCount rootWidth node first count (columns+rows) 0 0 hnode hn hw _ _ _ hf hs

#print axioms At.preserve_before
end Maxwell.Cost.RoutingPorts.Complete.Tree.Outputs
