import Maxwell.Cost.BinarySplit.Run

namespace Maxwell.Cost.BinarySplit
open Structured

/-- All finite word widths and addresses consulted by a split node. -/
def budget (layout : Layout) (n : ℕ) : ℕ :=
  DoublingPass.budget layout.route n.bits + layout.forward.bits.length + layout.backward.bits.length +
    2*layout.pairing.bits.length + 2*layout.conjugated.bits.length + 10

theorem half_budget (layout : Layout) (n : ℕ) : DoublingInit.budget layout.half n.bits ≤ budget layout n := by
  dsimp [budget,DoublingInit.budget,DoublingPass.budget,Layout.half]
  omega

theorem conjugate_budget (layout : Layout) (n : ℕ) : DoublingPass.budget layout.conjugate n.bits ≤ budget layout n := by
  dsimp [budget,DoublingPass.budget,Layout.conjugate]
  omega

theorem cycle_budget (layout : Layout) (n : ℕ) : DoublingInit.budget layout.cycle n.bits ≤ budget layout n := by
  dsimp [budget,DoublingInit.budget,DoublingPass.budget,Layout.cycle]
  omega

private theorem metadata_length (layout : Layout) (n : ℕ) (current : DoublingPass.Layout)
    (clock : List Bool) (hc : clock.length=layout.route.width)
    (hw : current.width=layout.route.width)
    (h82 : current.oldJump.bits.length≤budget layout n)
    (h84 : current.oldMinimum.bits.length≤budget layout n)
    (h85 : current.newJump.bits.length≤budget layout n)
    (h86 : current.newMinimum.bits.length≤budget layout n)
    (i : ℕ) (hi : i∈metadataIds) : (metadata layout current clock i).length≤budget layout n := by
  simp only [metadataIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [metadata,Function.update_apply]
  all_goals norm_num [savedWords]
  all_goals try rw [hw]
  all_goals try rw [hc]
  all_goals dsimp [budget,DoublingPass.budget] at *
  all_goals omega

theorem conjugateCost_bound (layout : Layout) (n : ℕ) (clock : List Bool) (hc : clock.length=layout.route.width) :
    conjugateCost layout clock ≤ 84*budget layout n+85 := by
  have h := WordAssign.price_bound conjugateAssignments metadataIds (metadata layout layout.half.route clock)
    (budget layout n) (by simp [WordAssign.Valid,conjugateAssignments,metadataIds])
    (metadata_length layout n layout.half.route clock hc rfl
      (by dsimp [budget,DoublingPass.budget,Layout.half]; omega)
      (by dsimp [budget,DoublingPass.budget,Layout.half]; omega)
      (by dsimp [budget,DoublingPass.budget,Layout.half]; omega)
      (by dsimp [budget,DoublingPass.budget,Layout.half]; omega))
  change conjugateCost layout clock ≤ 4*(21*budget layout n+21)+1 at h
  omega

theorem cycleCost_bound (layout : Layout) (n : ℕ) (clock : List Bool) (hc : clock.length=layout.route.width) :
    cycleCost layout clock ≤ 84*budget layout n+85 := by
  have h := WordAssign.price_bound cycleAssignments metadataIds (metadata layout layout.conjugate clock)
    (budget layout n) (by simp [WordAssign.Valid,cycleAssignments,metadataIds])
    (metadata_length layout n layout.conjugate clock hc rfl
      (by dsimp [budget,DoublingPass.budget,Layout.conjugate]; omega)
      (by dsimp [budget,DoublingPass.budget,Layout.conjugate]; omega)
      (by dsimp [budget,DoublingPass.budget,Layout.conjugate]; omega)
      (by dsimp [budget,DoublingPass.budget,Layout.conjugate]; omega))
  change cycleCost layout clock ≤ 4*(21*budget layout n+21)+1 at h
  omega

/-- Charged node complexity, including both pairing constructions and all
metadata copying, is linear in tokens up to bit-width and doubling factors. -/
theorem costCap_bound (layout : Layout) (n : ℕ) (clock : List Bool) (hc : clock.length=layout.route.width) :
    costCap layout n clock ≤ 6000000*(n+1)*(n.bits.length+1)*(budget layout n+1)^2 := by
  let b := budget layout n
  have hp : HalfPair.passCost layout.half n ≤ 250000*(n+1)*(b+1)^2 :=
    (HalfPair.passCost_bound layout.half n).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (half_budget layout n) 1) 2))
  have hq : ConjugatePass.passCost layout.conjugate n ≤ 350000*(n+1)*(b+1)^2 :=
    (ConjugatePass.passCost_bound layout.conjugate n).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (conjugate_budget layout n) 1) 2))
  have hz : CycleSplit.costCap layout.cycle n ≤ 5000000*(n+1)*(n.bits.length+1)*(b+1)^2 :=
    (CycleSplit.costCap_bound layout.cycle n).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (cycle_budget layout n) 1) 2))
  have ha := conjugateCost_bound layout n clock hc
  have hb := cycleCost_bound layout n clock hc
  have hs : b+1≤(b+1)^2 := by nlinarith
  change _≤6000000*(n+1)*(n.bits.length+1)*(b+1)^2
  dsimp only [costCap]
  change conjugateCost layout clock≤84*b+85 at ha
  change cycleCost layout clock≤84*b+85 at hb
  nlinarith

end Maxwell.Cost.BinarySplit
