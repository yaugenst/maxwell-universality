import Maxwell.Cost.CycleSplit.Pipeline
import Maxwell.Cost.ColorPass.Complexity

namespace Maxwell.Cost.CycleSplit
open DoublingPass

theorem color_budget_bound (layout : DoublingInit.Layout) (k : ℕ) (index : List Bool) :
    budget (colorLayout (layoutAfter layout.route k) layout.inputA) index ≤ DoublingInit.budget layout index+1 := by
  have h := budget_layoutAfter layout.route k index
  simp only [budget,colorLayout,DoublingInit.budget] at *
  have hone : (1 : ℕ).bits.length = 1 := by decide
  have hw := layoutAfter_width layout.route k
  omega

theorem adapterCost_bound (layout : DoublingInit.Layout) (k : ℕ) (index : List Bool) :
    adapterCost (layoutAfter layout.route k) layout.inputA ≤ 30*DoublingInit.budget layout index+28 := by
  have h := budget_layoutAfter layout.route k index
  dsimp [adapterCost,DoublingInit.budget]
  simp only [budget] at *
  omega

theorem finishCost_bound (layout : Layout) (n : ℕ) :
    finishCost layout n ≤ 350000*(n+1)*(budget layout n.bits+1)^2 := by
  have h := ColorPass.loopCost_bound layout n
  have hl : n.bits.length≤budget layout n.bits := by dsimp [budget]; omega
  have hb : budget layout n.bits+1≤(budget layout n.bits+1)^2 := by nlinarith
  dsimp [finishCost]
  nlinarith

/-- Complete charged binary cycle splitting is near-linear in the number
of tokens, including initialization, computed doubling count, descriptor
updates, final colors, and all scratch reclamation. -/
theorem costCap_bound (layout : DoublingInit.Layout) (n : ℕ) :
    costCap layout n ≤ 5000000*(n+1)*(n.bits.length+1)*(DoublingInit.budget layout n.bits+1)^2 := by
  let b := DoublingInit.budget layout n.bits
  let l := n.bits.length
  let finalLayout := layoutAfter layout.route l
  have hinit := DoublingInit.passCost_bound layout n
  have hd0 := computedCost_bound layout.route n
  have hd : computedCost layout.route n ≤ 500000*(n+1)*(l+1)*(b+1)^2 := hd0.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [b,DoublingInit.budget]; omega) _))
  have ha : adapterCost finalLayout layout.inputA ≤ 30*b+28 := adapterCost_bound layout l n.bits
  have hf0 := finishCost_bound (colorLayout finalLayout layout.inputA) n
  have hbColor : budget (colorLayout finalLayout layout.inputA) n.bits+1 ≤ 2*(b+1) := by
    have h := color_budget_bound layout l n.bits
    dsimp [b,finalLayout] at *
    omega
  have hsquare : (budget (colorLayout finalLayout layout.inputA) n.bits+1)^2 ≤ 4*(b+1)^2 := by
    have h := Nat.pow_le_pow_left hbColor 2
    nlinarith
  have hf : finishCost (colorLayout finalLayout layout.inputA) n ≤ 1400000*(n+1)*(b+1)^2 :=
    hf0.trans (by nlinarith [Nat.mul_le_mul_left (350000*(n+1)) hsquare])
  have hb : b+1≤(b+1)^2 := by nlinarith
  change DoublingInit.passCost layout n ≤ 400000*(n+1)*(b+1)^2 at hinit
  change DoublingInit.passCost layout n+(computedCost layout.route n+
    (adapterCost finalLayout layout.inputA+finishCost (colorLayout finalLayout layout.inputA) n)) ≤
      5000000*(n+1)*(l+1)*(b+1)^2
  nlinarith

end Maxwell.Cost.CycleSplit
