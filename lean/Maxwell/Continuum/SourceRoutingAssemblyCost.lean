import Maxwell.Continuum.SourceRoutingAssemblyCleanup

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem assembly_budget (q : ℕ→ℕ) (k B : ℕ)
    (hn : q 801=2*2^k) (hw : q 802=k+2) (hq : ∀i∈controls,(q i).bits.length ≤ B) :
    ChildPermutation.budget (layout q) (2*2^k).bits ≤ 12*(B+2) := by
  have h0:=hq 800 (by decide)
  have h1:=hq 801 (by decide)
  have h2:=hq 802 (by decide)
  have h3:=hq 803 (by decide)
  have h4:=hq 804 (by decide)
  have h5:=hq 805 (by decide)
  have count:=NodeSetup.clock_length q k hn
  have childWidth := (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le (q 802) 1)).trans h2
  rw [hn] at count h1
  simp only [ChildPermutation.budget,layout,ChildPermutation.Layout.childWidth,
    show (0 : ℕ).bits.length=0 by decide]
  omega

theorem prepare_cost (q : ℕ→ℕ) (k B : ℕ)
    (hn : q 801=2*2^k) (hq : ∀i∈controls,(q i).bits.length ≤ B) :
    ChildPermutation.prepareCost (layout q) k (q 801).bits ≤ 2^10*(B+2) := by
  have h1:=hq 801 (by decide)
  have h2:=hq 802 (by decide)
  have h5:=hq 805 (by decide)
  dsimp only [ChildPermutation.prepareCost,layout]
  rw [hn] at h1 ⊢
  omega

theorem pass_cost (q : ℕ→ℕ) (k B : ℕ)
    (hn : q 801=2*2^k) (hw : q 802=k+2) (hq : ∀i∈controls,(q i).bits.length ≤ B) :
    ColorAssemble.passCost (layout q) k ≤ 2^28*(q 801+1)*(B+2)^2 := by
  have budget:=assembly_budget q k B hn hw hq
  have big : ChildPermutation.budget (layout q) (2*2^k).bits+1 ≤ 13*(B+2) := by omega
  have hh:=ColorAssemble.passCost_bound (layout q) k
  have hsquare:=Nat.pow_le_pow_left big 2
  rw [hn]
  calc
    _ ≤ 300000*(2*2^k+1)*(13*(B+2))^2 := hh.trans (Nat.mul_le_mul_left _ hsquare)
    _ = (300000*13^2)*((2*2^k+1)*(B+2)^2) := by ring
    _ ≤ _ := by rw [mul_assoc (2^28)];exact Nat.mul_le_mul_right _ (by norm_num)

theorem cleanup_cost (q : ℕ→ℕ) (k B : ℕ) (hB : 1 ≤ B)
    (hn : q 801=2*2^k) (hw : q 802=k+2) (hq : ∀i∈controls,(q i).bits.length ≤ B)
    (clock childClock : List Bool) (hc : clock.length=q 802) (hcc : childClock.length=q 802-1) :
    17*(6*WordCleanup.wordBudget (cleanupEntries q k clock childClock)+4)+1 ≤ 2^12*(B+2) := by
  have h:=cleanup_budget q k B hB hn hw hq clock childClock hc hcc
  omega

#print axioms pass_cost
end Maxwell.Cost.RoutingPorts.Complete.Tree.Assembly
