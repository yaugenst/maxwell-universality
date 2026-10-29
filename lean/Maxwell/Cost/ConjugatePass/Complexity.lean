import Maxwell.Cost.ConjugatePass.Correctness

namespace Maxwell.Cost.ConjugatePass
open DoublingPass

/-- Charged cost of the finite conjugation pass, including counter traversal
and workspace cleanup, is linear in slot count and quadratic in word budget. -/
theorem loopCost_bound (layout : Layout) (n : ℕ) :
    loopCost layout n ≤ 300000*(n+1)*(budget layout n.bits+1)^2 := by
  let b := budget layout n.bits
  have hl : n.bits.length ≤ b := by dsimp [b,budget]; omega
  have hb : b+1 ≤ (b+1)^2 := by nlinarith
  have hcounter : (n+1)*(13*n.bits.length+15) ≤ (n+1)*(28*(b+1)^2) := by
    apply Nat.mul_le_mul_left
    nlinarith
  dsimp [loopCost]
  change _ ≤ 300000*(n+1)*(b+1)^2
  nlinarith

theorem passCost_bound (layout : Layout) (n : ℕ) :
    passCost layout n ≤ 350000*(n+1)*(budget layout n.bits+1)^2 := by
  have h := loopCost_bound layout n
  have hl : n.bits.length ≤ budget layout n.bits := by dsimp [budget]; omega
  have hb : budget layout n.bits+1 ≤ (budget layout n.bits+1)^2 := by nlinarith
  dsimp [passCost]
  nlinarith

end Maxwell.Cost.ConjugatePass
