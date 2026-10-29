import Maxwell.Cost.RoutingAllocator.Plan

namespace Maxwell.Cost.RoutingAllocator
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

structure Result (v : ℕ → ℕ) (clock : List Bool) (s : BitRAMState) : Prop where
  config : DoublingInit.Config (layout (v 190) (v 191) (v 192) (v 193) (v 194)).split.half [] clock s
  saved : BinarySplit.Saved (layout (v 190) (v 191) (v 192) (v 193) (v 194)).split s
  children : ∀i : Fin 4, Word s (122+i.val)
    ((layout (v 190) (v 191) (v 192) (v 193) (v 194)).childBases i).bits
  count : Word s 96 (v 191).bits
  frontier : Word s 190 (nextFrontier (v 190) (v 191) (v 192)).bits
  parent : Word s 195 (parentOutput (v 190) (v 191) (v 192)).bits
  stride : Word s 196 ((v 191)*(v 192)).bits

private theorem result_of_bank (v : ℕ → ℕ) (clock : List Bool) (s : BitRAMState)
    (bank : NatAssign.Bank ids (outputValues v) s) (hclock : Word s 83 clock) : Result v clock s := by
  constructor
  · refine ⟨⟨?_,?_,?_,hclock,?_,?_,?_⟩,?_,?_⟩
    · convert bank 80 (by decide) using 1 <;> norm_num [outputValues,layout,BinarySplit.Layout.half]
    · convert bank 81 (by decide) using 1 <;> norm_num [outputValues]
    · convert bank 82 (by decide) using 1 <;> norm_num [outputValues,layout,BinarySplit.Layout.half]
    · convert bank 84 (by decide) using 1 <;> norm_num [outputValues,layout,BinarySplit.Layout.half]
    · convert bank 85 (by decide) using 1 <;> norm_num [outputValues,layout,BinarySplit.Layout.half]
    · convert bank 86 (by decide) using 1 <;> norm_num [outputValues,layout,BinarySplit.Layout.half,slab]
    · convert bank 98 (by decide) using 1 <;> norm_num [outputValues,layout,BinarySplit.Layout.half,slab]
    · convert bank 99 (by decide) using 1 <;> norm_num [outputValues,layout,BinarySplit.Layout.half]
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · convert bank 100 (by decide) using 1 <;> norm_num [outputValues,layout]
    · convert bank 101 (by decide) using 1 <;> norm_num [outputValues,layout]
    · convert bank 102 (by decide) using 1 <;> norm_num [outputValues,layout]
    · convert bank 103 (by decide) using 1 <;> norm_num [outputValues,layout]
    · convert bank 104 (by decide) using 1 <;> norm_num [outputValues,layout]
    · convert bank 105 (by decide) using 1 <;> norm_num [outputValues,layout]
  · intro i
    fin_cases i
    · convert bank 122 (by decide) using 1 <;> norm_num [outputValues,layout]
    · convert bank 123 (by decide) using 1 <;> norm_num [outputValues,layout]
    · convert bank 124 (by decide) using 1 <;> norm_num [outputValues,layout]
    · convert bank 125 (by decide) using 1 <;> norm_num [outputValues,layout]
  · convert bank 96 (by decide) using 1 <;> norm_num [outputValues]
  · convert bank 190 (by decide) using 1 <;> norm_num [outputValues]
  · convert bank 195 (by decide) using 1 <;> norm_num [outputValues]
  · convert bank 196 (by decide) using 1 <;> norm_num [outputValues]

/-- Actual arithmetic computes every descriptor and advances the heap. The
entire memory and every tape outside the explicit finite work set are kept. -/
theorem executes (v : ℕ → ℕ) (clock : List Bool) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val)
    (hclock : Word s.val 83 clock) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ price v ∧ Result v clock t.val ∧
      NatAssign.Bank ids (outputValues v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨cost,t,he,hcost,hbank,hs,hf⟩ := NatAssign.executes ids ids_lower statements valid v input tape s bank scratch
  have hb : NatAssign.Bank ids (outputValues v) t.val := by
    intro i hi
    rw [←values_at v i hi]
    exact hbank i hi
  have hc : Word t.val 83 clock := BankArray.word_of_eq (hf.tapes 83 (by decide)) hclock
  exact ⟨cost,t,he,hcost,result_of_bank v clock t.val hb hc,hb,hs,hf⟩

/-- The bound includes clearing previous descriptor words and all copies,
products, additions and the final canonical zero. -/
theorem executes_bounded (v : ℕ → ℕ) (clock : List Bool) (B : ℕ)
    (hv : ∀i∈ids,(v i).bits.length ≤ B) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val)
    (hclock : Word s.val 83 clock) :
    ∃ cost t, Executes input tape code cost s t ∧
      cost ≤ 3000*8^statements.length*(B+2)^2 ∧ Result v clock t.val ∧
      NatAssign.Bank ids (outputValues v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes v clock input tape s bank scratch hclock
  exact ⟨cost,t,he,hcost.trans (price_bound v B hv),ht⟩

theorem compiled_run (v : ℕ → ℕ) (clock : List Bool) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val)
    (hclock : Word s.val 83 clock) :
    ∃ t : Store, (runPriced (code.compile.next input tape) (price v+1) s.val).finished=some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (price v+1) s.val).instructions ≤ price v ∧
      Result v clock t.val ∧ NatAssign.Bank ids (outputValues v) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes v clock input tape s bank scratch hclock
  have hr := he.compiled_run (price v+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

theorem frontier_bits (frontier n width : ℕ) :
    (nextFrontier frontier n width).bits.length ≤ frontier.bits.length+n.bits.length+width.bits.length+5 := by
  have ha := RationalAccumulator.bits_add_le frontier (11*(n*width))
  have hm := RationalAccumulator.bits_mul_le n width
  have hh := RationalAccumulator.bits_mul_le 11 (n*width)
  have h11 : (11:ℕ).bits.length=4 := by decide
  dsimp [nextFrontier,slab]
  rw [h11] at hh
  omega

end Maxwell.Cost.RoutingAllocator
