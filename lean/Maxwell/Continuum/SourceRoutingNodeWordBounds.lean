import Maxwell.Continuum.SourceRoutingPrivateVisit
import Maxwell.Continuum.NatAssignOutputWidth

/-! Every node operand has logarithmic width in its count and heap
addresses. Pointer doubling only exchanges four bounded descriptors. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.NodeWords
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def plainLayout (q : ℕ→ℕ) : SplitNode.Layout :=
  RoutingAllocator.layout (q 800) (q 801) (q 802) (q 803) (q 804)

theorem layout_eq (q : ℕ→ℕ) : Node.layout (NodeSetup.descriptor q)=plainLayout q := by
  simp [Node.layout,NodeSetup.descriptor,plainLayout]

theorem after_eq (l : DoublingPass.Layout) (r : ℕ) :
    DoublingPass.layoutAfter l r=l ∨ DoublingPass.layoutAfter l r=l.flip := by
  induction r with
  | zero => exact Or.inl rfl
  | succ r ih =>
    rcases ih with h|h
    · exact Or.inr (by simp only [DoublingPass.layoutAfter,h])
    · exact Or.inl (by simp only [DoublingPass.layoutAfter,h,DoublingPass.Layout.flip_flip])

theorem slab_bits (q : ℕ→ℕ) (B : ℕ)
    (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B) (j : ℕ) (hj : j ≤ 11) :
    (RoutingAllocator.slab (q 800) (q 801) (q 802) j).bits.length ≤ 3*B+5 := by
  have hh : RoutingAllocator.slab (q 800) (q 801) (q 802) j ≤
      RoutingAllocator.nextFrontier (q 800) (q 801) (q 802) := by
    unfold RoutingAllocator.slab RoutingAllocator.nextFrontier
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  have hb := Maxwell.Continuum.RationalWords.bits_mono hh
  have hf := RoutingAllocator.frontier_bits (q 800) (q 801) (q 802)
  have h0 := hq 800 (by decide)
  have h1 := hq 801 (by decide)
  have h2 := hq 802 (by decide)
  omega

theorem route_after_bits (q : ℕ→ℕ) (B r : ℕ)
    (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B) :
    (DoublingPass.layoutAfter (plainLayout q).split.route r).oldJump.bits.length ≤ 3*B+5 ∧
    (DoublingPass.layoutAfter (plainLayout q).split.route r).oldMinimum.bits.length ≤ 3*B+5 ∧
    (DoublingPass.layoutAfter (plainLayout q).split.route r).newJump.bits.length ≤ 3*B+5 ∧
    (DoublingPass.layoutAfter (plainLayout q).split.route r).newMinimum.bits.length ≤ 3*B+5 := by
  rcases after_eq (plainLayout q).split.route r with h|h
  all_goals rw [h]
  all_goals dsimp only [plainLayout,RoutingAllocator.layout,DoublingPass.Layout.flip]
  all_goals exact ⟨slab_bits q B hq _ (by omega),slab_bits q B hq _ (by omega),
    slab_bits q B hq _ (by omega),slab_bits q B hq _ (by omega)⟩

theorem split_budget (q : ℕ→ℕ) (k B : ℕ) (hn : q 801=2*2^k) (hw : q 802=k+2)
    (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B) :
    SplitNode.budget (Node.layout (NodeSetup.descriptor q)) k ≤ 128*(B+2) := by
  have hnBits := hq 801 (by decide)
  have hwBits := hq 802 (by decide)
  have hfBits := hq 803 (by decide)
  have hbBits := hq 804 (by decide)
  have hwidth : q 802 ≤ B := by rw [hw]; rw [NodeSetup.clock_length q k hn] at hnBits; exact hnBits
  have childBits : (q 802-1).bits.length ≤ B :=
    (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le _ _)).trans hwBits
  have childCountBits : (2^k).bits.length ≤ B := by
    exact (Maxwell.Continuum.RationalWords.bits_mono (show 2^k ≤ q 801 by rw [hn]; omega)).trans hnBits
  have h0 := slab_bits q B hq 0 (by omega)
  have h1 := slab_bits q B hq 1 (by omega)
  have h2 := slab_bits q B hq 2 (by omega)
  have h3 := slab_bits q B hq 3 (by omega)
  have h4 := slab_bits q B hq 4 (by omega)
  have h5 := slab_bits q B hq 5 (by omega)
  have h6 := slab_bits q B hq 6 (by omega)
  have h7 := slab_bits q B hq 7 (by omega)
  have h8 := slab_bits q B hq 8 (by omega)
  have h9 := slab_bits q B hq 9 (by omega)
  have ha := (route_after_bits q B (2*2^k).bits.length hq).2.2.1
  rw [layout_eq]
  dsimp only [SplitNode.budget,BinarySplit.budget,DoublingPass.budget,ChildPermutation.budget,
    SplitNode.Layout.child,ChildPermutation.Layout.childWidth,BinarySplit.finalLayout,CycleSplit.colorLayout]
  change (DoublingPass.layoutAfter (plainLayout q).split.route (2*2^k).bits.length).newJump.bits.length ≤ _ at ha
  dsimp only [plainLayout,RoutingAllocator.layout] at ha ⊢
  rw [←hn] at *
  change (RoutingAllocator.slab (q 800) (q 801) (q 802) (6+((2 : Fin 4) : ℕ))).bits.length ≤ 3*B+5 at h8
  change (RoutingAllocator.slab (q 800) (q 801) (q 802) (6+((3 : Fin 4) : ℕ))).bits.length ≤ 3*B+5 at h9
  simp only [Fin.val_zero, Fin.val_one, Nat.reduceAdd] at *
  omega

#print axioms split_budget

end Maxwell.Cost.RoutingPorts.Complete.Tree.NodeWords
