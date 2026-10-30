import Maxwell.Continuum.SourceRoutingTreeLayout
import Maxwell.Continuum.SourceRoutingPrivateVisit

/-! A split visit writes only inside its own fixed-stride node block.
All previously produced arrays in other blocks remain represented. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Memory
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def Frame (base length : ℕ) (before after : ℕ→Bool) : Prop :=
  ∀p,p<base ∨ base+length ≤ p → after p=before p

theorem Frame.refl (base length : ℕ) (memory : ℕ→Bool) : Frame base length memory memory := fun _ _ => rfl
theorem Frame.trans {base length : ℕ} {a b c : ℕ→Bool} (h : Frame base length a b)
    (j : Frame base length b c) : Frame base length a c := fun p hp => (j p hp).trans (h p hp)

theorem split_frame (heap rootCount rootWidth node k : ℕ) (hn : 2*2^k ≤ rootCount)
    (hw : k+2 ≤ rootWidth) (forward backward : ℕ) (before after : ℕ→Bool)
    (hf : SplitNode.MemoryFrame
      (RoutingAllocator.layout (block heap rootCount rootWidth node) (2*2^k) (k+2) forward backward)
      k before after) : Frame (block heap rootCount rootWidth node) (stride rootCount rootWidth) before after := by
  intro p hp
  have slot (j : ℕ) (hj : j<11) :
      p<RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) j ∨
      RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) j+(2*2^k)*(k+2) ≤ p := by
    have hh := slab_fits heap rootCount rootWidth node (2*2^k) (k+2) j hn hw hj
    rcases hp with hp|hp
    · exact Or.inl (hp.trans_le hh.1)
    · exact Or.inr (hh.2.trans hp)
  apply hf p
  · exact ⟨slot 0 (by omega),slot 1 (by omega),slot 2 (by omega),slot 3 (by omega),
      slot 4 (by omega),slot 5 (by omega)⟩
  · intro i
    rw [SplitNode.Layout.child_outputBase]
    change p<RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) (6+i.val) ∨
      RoutingAllocator.slab (block heap rootCount rootWidth node) (2*2^k) (k+2) (6+i.val)+2^k*(k+2-1) ≤ p
    have hsize : 2^k*(k+2-1) ≤ (2*2^k)*(k+2) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
    rcases slot (6+i.val) (by omega) with hs|hs
    · exact Or.inl hs
    · right; omega

theorem Frame.represents {base length array width n : ℕ} {before after : ℕ→Bool}
    {values : Vector (List Bool) n} (hf : Frame base length before after)
    (hs : IncidenceEncoding.Separated array (n*width) base length)
    (hr : BitArray.Represents before array width values) :
    BitArray.Represents after array width values := BinarySplit.represents_outside hf hs hr

theorem other_block (heap rootCount rootWidth a b base n width : ℕ)
    (hab : a≠b) (hlo : block heap rootCount rootWidth a ≤ base)
    (hhi : base+n*width ≤ block heap rootCount rootWidth a+stride rootCount rootWidth) :
    IncidenceEncoding.Separated base (n*width) (block heap rootCount rootWidth b) (stride rootCount rootWidth) := by
  rcases block_separated heap rootCount rootWidth a b hab with hs|hs
  · exact Or.inl (hhi.trans hs)
  · exact Or.inr (hs.trans hlo)

#print axioms split_frame
#print axioms other_block
end Maxwell.Cost.RoutingPorts.Complete.Tree.Memory
