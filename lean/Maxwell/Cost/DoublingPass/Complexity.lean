import Maxwell.Cost.DoublingPass.Computed

namespace Maxwell.Cost.DoublingPass

/-- Binary representation length is at most the represented natural. -/
theorem bits_length_le_self (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr n.lt_two_pow_self

/-- This bound concerns the actual finite traversal and every descriptor
swap, not a count attached to the pure array function. -/
theorem roundCost_bound (layout : Layout) (n : ℕ) :
    roundCost layout n ≤ 400000*(n+1)*(budget layout n.bits+1)^2 := by
  let b := budget layout n.bits
  have hl : n.bits.length ≤ b := by dsimp [b,budget]; omega
  have hs : layout.oldJump.bits.length+layout.oldMinimum.bits.length+
      layout.newJump.bits.length+layout.newMinimum.bits.length ≤ b := by dsimp [b,budget]; omega
  have hb : b+1 ≤ (b+1)^2 := by nlinarith
  have hcounter : (n+1)*(13*n.bits.length+15) ≤ (n+1)*(28*(b+1)^2) := by
    apply Nat.mul_le_mul_left
    nlinarith
  dsimp [roundCost,passCost,loopCost,swapCost]
  change _ ≤ 400000*(n+1)*(b+1)^2
  nlinarith

/-- Computing the round count, all repeated array passes, and final cleanup
cost O(n log n) times a fixed quadratic polynomial in the address/word widths. -/
theorem computedCost_bound (layout : Layout) (n : ℕ) :
    computedCost layout n ≤ 500000*(n+1)*(n.bits.length+1)*(budget layout n.bits+1)^2 := by
  let l := n.bits.length
  let b := budget layout n.bits
  have hl : l ≤ b := by dsimp [l,b,budget]; omega
  have hll : l.bits.length ≤ l := bits_length_le_self l
  have hb : b+1 ≤ (b+1)^2 := by nlinarith
  have hlsq : (l+1)^2 ≤ (b+1)^2 := Nat.pow_le_pow_left (by omega) _
  have hc : (l+1)*(13*l.bits.length+15) ≤ (l+1)*(28*(b+1)^2) := by
    apply Nat.mul_le_mul_left
    nlinarith
  have hr := Nat.mul_le_mul_left l (roundCost_bound layout n)
  dsimp [computedCost,roundsCost]
  change 48*(l+1)^2+1+((l+1)*(13*l.bits.length+15)+l*roundCost layout n+6*l.bits.length+4) ≤ _
  change _ ≤ 500000*(n+1)*(l+1)*(b+1)^2
  change l*roundCost layout n ≤ l*(400000*(n+1)*(b+1)^2) at hr
  nlinarith

end Maxwell.Cost.DoublingPass
