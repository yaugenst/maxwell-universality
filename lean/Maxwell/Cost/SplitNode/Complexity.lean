import Maxwell.Cost.SplitNode.Run

namespace Maxwell.Cost.SplitNode

/-- Complete actual address and word budget for one parent and its four outputs. -/
def budget (layout : Layout) (k : ℕ) : ℕ :=
  BinarySplit.budget layout.split (2*(2^k)) +
    ChildPermutation.budget (layout.child (2*(2^k))) (2^k).bits +
    (2*(2^k)).bits.length+1

/-- Linear token work, a logarithmic number of doubling rounds, and quadratic
bit-word arithmetic, including the executed child-metadata construction. -/
theorem costCap_bound (layout : Layout) (k : ℕ) (clock : List Bool)
    (hc : clock.length=layout.split.route.width) :
    costCap layout k clock ≤ 7000000*(2*(2^k)+1)*((2*(2^k)).bits.length+1)*(budget layout k+1)^2 := by
  let n := 2*(2^k)
  let b := budget layout k
  have hsplit : BinarySplit.budget layout.split n≤b := by dsimp [b,budget,n]; omega
  have hchild : ChildPermutation.budget (layout.child n) (2^k).bits≤b := by dsimp [b,budget,n]; omega
  have hnlen : n.bits.length≤b := by dsimp [b,budget,n]; omega
  have ha := (BinarySplit.costCap_bound layout.split n clock hc).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hsplit 1) 2))
  have hc' := (ChildPermutation.passCost_bound (layout.child n) k).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hchild 1) 2))
  have hwidth : layout.split.route.width≤b := by
    dsimp [BinarySplit.budget,DoublingPass.budget] at hsplit
    omega
  have hwidthlen : (layout.child n).parentWidth.bits.length≤b := by
    dsimp [ChildPermutation.budget] at hchild
    omega
  have hcolorlen : (layout.child n).colors.bits.length≤b := by
    dsimp [ChildPermutation.budget] at hchild
    omega
  have hb : ChildPermutation.prepareCost (layout.child n) k clock≤104*b+123 := by
    dsimp only [ChildPermutation.prepareCost]
    rw [hc]
    change 44*(layout.child n).parentWidth.bits.length+30*layout.split.route.width+15*n.bits.length+
      15*(layout.child n).colors.bits.length+123≤104*b+123
    omega
  have hs : b+1≤(b+1)^2 := by nlinarith
  change _≤7000000*(n+1)*(n.bits.length+1)*(b+1)^2
  dsimp only [costCap]
  change _+ (ChildPermutation.prepareCost (layout.child n) k clock+_)≤_
  have hm : 2^k≤n := by dsimp [n]; omega
  have hscale : (b+1)^2≤(n+1)*(n.bits.length+1)*(b+1)^2 := by
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have hc'' : ChildPermutation.passCost (layout.child n) k ≤
      650000*(n+1)*(n.bits.length+1)*(b+1)^2 := by
    apply hc'.trans
    have hfactor : 2^k+1≤(n+1)*(n.bits.length+1) := by nlinarith
    nlinarith [Nat.mul_le_mul_right ((b+1)^2) hfactor]
  change BinarySplit.costCap layout.split n clock+
    (ChildPermutation.prepareCost (layout.child n) k clock+ChildPermutation.passCost (layout.child n) k)≤_
  nlinarith

end Maxwell.Cost.SplitNode
