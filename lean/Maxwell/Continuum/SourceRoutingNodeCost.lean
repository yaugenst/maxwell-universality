import Maxwell.Continuum.SourceRoutingNodeWordBounds

/-! The actual reusable node program has linear token cost times a cubic
word-length factor. Its cleanup is charged, including the two clocks. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.NodeWords
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

private theorem wordBudget_le (entries : List (ℕ×List Bool)) (B : ℕ)
    (h : ∀a∈entries,a.2.length ≤ B) : WordCleanup.wordBudget entries ≤ entries.length*B := by
  induction entries with
  | nil => simp [WordCleanup.wordBudget]
  | cons a rest ih =>
    have ha := h a (by simp)
    have hr := ih (fun a ha => h a (by simp [ha]))
    simp only [WordCleanup.wordBudget,List.map_cons,List.sum_cons,List.length_cons]
    dsimp only [WordCleanup.wordBudget] at hr
    nlinarith only [ha,hr]

theorem cleanup_budget (q : ℕ→ℕ) (k B : ℕ) (hn : q 801=2*2^k) (hw : q 802=k+2)
    (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B) :
    Node.cleanupBudget (NodeSetup.descriptor q) k ≤ 256*(B+2) := by
  have hhead := hq 800 (by decide)
  have hnBits := hq 801 (by decide)
  have hwBits := hq 802 (by decide)
  have hfBits := hq 803 (by decide)
  have hbBits := hq 804 (by decide)
  have hcountBits : (2*2^k).bits.length ≤ B := by rw [←hn]; exact hnBits
  have hwidth : q 802 ≤ B := by
    rw [hw]; rw [NodeSetup.clock_length q k hn] at hnBits; exact hnBits
  have childBits : (q 802-1).bits.length ≤ B :=
    (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le _ _)).trans hwBits
  have childCountBits : (2^k).bits.length ≤ B :=
    (Maxwell.Continuum.RationalWords.bits_mono (show 2^k ≤ q 801 by rw [hn]; omega)).trans hnBits
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
  have h10 := slab_bits q B hq 10 (by omega)
  have h11 := slab_bits q B hq 11 (by omega)
  have hprod : ((q 801)*(q 802)).bits.length ≤ 2*B := by
    exact (RationalAccumulator.bits_mul_le _ _).trans (by omega)
  have headers (i : ℕ) (hi : 190 ≤ i ∧ i ≤ 196) :
      (RoutingAllocator.outputValues (NodeSetup.descriptor q) i).bits.length ≤ 3*B+5 := by
    rcases hi with ⟨hi,hj⟩
    interval_cases i
    all_goals dsimp [RoutingAllocator.outputValues,NodeSetup.descriptor,
      RoutingAllocator.nextFrontier,RoutingAllocator.parentOutput]
    all_goals omega
  have ha := route_after_bits q B (2*2^k).bits.length hq
  change WordCleanup.wordBudget (NodeCleanup.entries (plainLayout q) k
    (List.replicate (q 802) false) (List.replicate (q 802-1) false)
    (RoutingAllocator.outputValues (NodeSetup.descriptor q))) ≤ _
  apply (wordBudget_le _ (3*B+5) ?_).trans (show 41*(3*B+5) ≤ 256*(B+2) by omega)
  intro a ha'
  simp only [NodeCleanup.entries,List.mem_cons,List.not_mem_nil,or_false] at ha'
  rcases ha' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.length_nil,List.length_cons,List.length_replicate,
    SplitNode.Layout.child_outputBase]
  all_goals first
    | exact headers _ (by omega)
    | (try dsimp only [SplitNode.Layout.child,ChildPermutation.Layout.childWidth,
        BinarySplit.finalLayout,CycleSplit.colorLayout,BinarySplit.Layout.half,
        plainLayout,RoutingAllocator.layout];
       first
       | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5
       | exact h6 | exact h7 | exact h8 | exact h9
       | exact ha.2.1 | exact ha.2.2.1
       | omega)

theorem visit_bound (q : ℕ→ℕ) (k B : ℕ) (hn : q 801=2*2^k) (hw : q 802=k+2)
    (hq : ∀i∈NodeSetup.controls,(q i).bits.length ≤ B) :
    NodeVisit.bound q k B+1 ≤ 2^180*(q 801+1)*(B+2)^3 := by
  have hs := split_budget q k B hn hw hq
  have hc := cleanup_budget q k B hn hw hq
  have hb := hq 801 (by decide)
  have hsplit : SplitNode.budget (Node.layout (NodeSetup.descriptor q)) k+1 ≤ 129*(B+2) := by omega
  have hsq := Nat.pow_le_pow_left hsplit 2
  have hcount : (2*2^k).bits.length+1 ≤ B+2 := by rw [←hn]; omega
  have hcost : 7000000*(2*2^k+1)*((2*2^k).bits.length+1)*
      (SplitNode.budget (Node.layout (NodeSetup.descriptor q)) k+1)^2 ≤
        (7000000*129^2)*(q 801+1)*(B+2)^3 := by
    calc
      _ ≤ 7000000*(2*2^k+1)*(B+2)*(129*(B+2))^2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hcount) hsq
      _ = _ := by rw [←hn]; ring
  have hB : B+2 ≤ (B+2)^3 := by nlinarith
  have hB2 : (B+2)^2 ≤ (B+2)^3 := by nlinarith
  have hscale : (B+2)^3 ≤ (q 801+1)*(B+2)^3 := Nat.le_mul_of_pos_left _ (by omega)
  have halloc : 3000*8^RoutingAllocator.statements.length=3000*8^33 := by rfl
  simp only [NodeVisit.bound,NodeSetup.bound,Node.costBound,halloc]
  nlinarith only [hcost,hc,hB,hB2,hscale]

#print axioms cleanup_budget
#print axioms visit_bound
end Maxwell.Cost.RoutingPorts.Complete.Tree.NodeWords
