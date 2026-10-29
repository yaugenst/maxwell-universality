import Maxwell.Cost.ColorAssemble.Public

namespace Maxwell.Cost.ColorAssemble
open ChildPermutation (Layout budget)

/-- One traversal is linear in the number of parent entries and quadratic
in the complete stored word/address budget. -/
theorem loopCost_bound (layout : Layout) (k : ℕ) :
    loopCost layout k ≤ 250000*(2*(2^k)+1)*(budget layout (2*(2^k)).bits+1)^2 := by
  let b := budget layout (2*(2^k)).bits
  have hl : (2*(2^k)).bits.length ≤ b := by dsimp [b,budget]; omega
  have hb : b+1 ≤ (b+1)^2 := by nlinarith
  have hcounter : (2*(2^k)+1)*(13*(2*(2^k)).bits.length+15) ≤ (2*(2^k)+1)*(28*(b+1)^2) := by
    apply Nat.mul_le_mul_left
    nlinarith
  dsimp [loopCost]
  change _ ≤ 250000*(2*(2^k)+1)*(b+1)^2
  nlinarith

theorem passCost_bound (layout : Layout) (k : ℕ) :
    passCost layout k ≤ 300000*(2*(2^k)+1)*(budget layout (2*(2^k)).bits+1)^2 := by
  have h := loopCost_bound layout k
  have hl : (2*(2^k)).bits.length ≤ budget layout (2*(2^k)).bits := by dsimp [budget]; omega
  have hb : budget layout (2*(2^k)).bits+1 ≤ (budget layout (2*(2^k)).bits+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul_right ((budget layout (2*(2^k)).bits+1)^2)
    (Nat.succ_le_succ (Nat.zero_le (2*((2:ℕ)^k))))
  dsimp [passCost]
  nlinarith

end Maxwell.Cost.ColorAssemble
