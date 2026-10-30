import Maxwell.Continuum.RationalDataflowDenominatorProduct
import Maxwell.Continuum.RationalDataflowArraySumMachine

/-! Polynomial bit cost for the literal raw-denominator product. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem denominatorCost_polynomial (n W wordLength : ℕ) :
    denominatorCost n W wordLength≤2^110*(n+1)^3*(W+2)^2+(n+1)*(13*wordLength+15) := by
  have hstage : stageCost (sumWidth n W)≤operationCost (sumWidth n W)+1 := by
    unfold stageCost operationCost
    have hpow := Nat.pow_le_pow_left (show sumWidth n W+2≤sumWidth n W+3 by omega) 2
    calc
      _ ≤ 2^96*(sumWidth n W+3)^2 := Nat.mul_le_mul_left _ hpow
      _ ≤ 2^100*(sumWidth n W+3)^2 := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ _ := Nat.le_succ _
  have hcost : denominatorCost n W wordLength≤sumCost n W wordLength := by
    have hm := Nat.mul_le_mul_left n (Nat.add_le_add_left hstage (2^20*(sumWidth n W+5)^2))
    simp only [← Nat.add_assoc] at hm
    unfold denominatorCost sumCost
    omega
  exact hcost.trans (sumCost_polynomial n W wordLength)

theorem denominator_product_computes {n : ℕ} (a : Table n) (S : Finset ℕ)
    (accumulator entry : ℕ) (hacc : accumulator∈S) (hentry : entry∈S) (hne : accumulator≠entry)
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W) (haWidth : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ t output,
      (runPriced ((denominatorCode accumulator entry).compile.next input tape)
        (denominatorCost n W xs.length+1) s.val).finished=
          some (t.place (denominatorCode accumulator entry).size) ∧
      (runPriced ((denominatorCode accumulator entry).compile.next input tape)
        (denominatorCost n W xs.length+1) s.val).instructions≤
          2^110*(n+1)^3*(W+2)^2+(n+1)*(13*xs.length+15) ∧
      RationalDataflow.Ready S output t ∧ a.Ready t ∧
      output accumulator=⟨∏ i : Fin n, (a.get i).denominator,0,1⟩ := by
  obtain ⟨cost,t,output,hex,hcost,hbank,harray,hvalue⟩ := denominator_product_executes a S accumulator entry
    hacc hentry hne W hW hmeta haWidth v hv input tape xs origin hlen s hn hcount hs ha
  obtain ⟨hrun,hsteps⟩ := hex.compiled_run (denominatorCost n W xs.length+1) (by omega)
  exact ⟨t,output,hrun,hsteps ▸ hcost.trans (denominatorCost_polynomial n W xs.length),hbank,harray,hvalue⟩

#print axioms denominator_product_computes
end Maxwell.Continuum.RationalDataflow.PartArray
