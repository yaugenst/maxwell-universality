import Maxwell.Cost.SignedRound.Kernel

namespace Maxwell.Cost.SignedRound

open Structured RationalAccumulator

def Output (s : BitRAMState) (z : ℤ) : Prop :=
  ∃ origin, s.tapes 4 = BitTape.shifted z.natAbs.bits origin ∧
    s.registers 23 = decide (z < 0)

theorem rounded_natAbs (negative : Bool) (numerator denominator : ℕ) :
    (rounded negative numerator denominator).natAbs = magnitude negative numerator denominator := by
  cases negative <;> simp [rounded]

/-- The scaled numerator is physically present on input tape 3. The actual
finite rounding program returns exactly the manuscript's dyadic numerator;
constructing the scale is a separate, charged caller operation. -/
theorem nearest_executes (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (negative : Bool) (numerator denominator precision : ℕ) (hd : 0 < denominator)
    (ao xo zo yo qo : ℤ)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.val.tapes 1 = BitTape.shifted denominator.bits xo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.val.tapes 3 = BitTape.shiftedEnd (numerator * 2^precision).bits yo)
    (h4 : s.val.tapes 4 = {BitTape.blank with head := qo})
    (hsign : s.val.registers 35 = negative) :
    ∃ cost, ∃ t : Store,
      cost ≤ 3000 * ((numerator * 2^precision).bits.length + denominator.bits.length + 2)^2 ∧
      Executes input tape code cost s t ∧
      Output t.val (Logical.Rounding.nearest precision
        ((if negative then -(numerator : ℚ) else numerator) / denominator)).numerator ∧
      t.val.tapes 1 = BitTape.shifted denominator.bits xo ∧
      Blank t.val 0 ∧ Blank t.val 2 ∧ Blank t.val 3 ∧ Frame 5 s.val t.val := by
  obtain ⟨cost, t, origin, hc, he, hw, hs, hden, hzero, htwo, hthree, hf⟩ :=
    executes input tape s negative (numerator * 2^precision) denominator hd
      ao xo zo yo qo h0 h1 h2 h3 h4 hsign
  refine ⟨cost, t, hc, he, ?_, hden, hzero, htwo, hthree, hf⟩
  rw [← rounded_dyadic negative numerator denominator precision hd]
  exact ⟨origin, by simpa only [rounded_natAbs] using hw, hs⟩

theorem nearest_compiled_run (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (negative : Bool) (numerator denominator precision : ℕ) (hd : 0 < denominator)
    (ao xo zo yo qo : ℤ)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.val.tapes 1 = BitTape.shifted denominator.bits xo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.val.tapes 3 = BitTape.shiftedEnd (numerator * 2^precision).bits yo)
    (h4 : s.val.tapes 4 = {BitTape.blank with head := qo})
    (hsign : s.val.registers 35 = negative) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape)
        (3000 * ((numerator * 2^precision).bits.length + denominator.bits.length + 2)^2 + 1)
        s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape)
        (3000 * ((numerator * 2^precision).bits.length + denominator.bits.length + 2)^2 + 1)
        s.val).instructions ≤
        3000 * ((numerator * 2^precision).bits.length + denominator.bits.length + 2)^2 ∧
      Output t.val (Logical.Rounding.nearest precision
        ((if negative then -(numerator : ℚ) else numerator) / denominator)).numerator ∧
      t.val.tapes 1 = BitTape.shifted denominator.bits xo ∧
      Blank t.val 0 ∧ Blank t.val 2 ∧ Blank t.val 3 ∧ Frame 5 s.val t.val := by
  obtain ⟨cost, t, hc, he, ho, hden, hzero, htwo, hthree, hf⟩ :=
    nearest_executes input tape s negative numerator denominator precision hd
      ao xo zo yo qo h0 h1 h2 h3 h4 hsign
  have hr := he.compiled_run
    (3000 * ((numerator * 2^precision).bits.length + denominator.bits.length + 2)^2 + 1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ho, hden, hzero, htwo, hthree, hf⟩

end Maxwell.Cost.SignedRound
