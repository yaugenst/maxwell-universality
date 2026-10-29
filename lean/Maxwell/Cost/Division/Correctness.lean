import Maxwell.Cost.Division.Loop
import Maxwell.Cost.Division.ReduceCycle

namespace Maxwell.Cost.Division

/-- Binary long division by the actual fixed program. The unprocessed dividend
prefix is the only loop variant; all scans and subroutine returns are charged. -/
theorem loop_simulation_full (input : List Bool) (tape : ℕ → Bool)
    (divisor : List Bool) (hd : 0 < divisor.length)
    (remaining remainder quotient : List Bool) (B : ℕ)
    (s : BitRAMState) (ao xo zo yo qo : ℤ)
    (hdB : divisor.length ≤ B) (hrB : remainder.length ≤ B)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = BitTape.shifted remainder ao)
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : PrefixTape (s.tapes 3) remaining yo)
    (h4 : s.tapes 4 = BitTape.shifted quotient qo) :
    ∃ cost t resultOrigin scratchOrigin quotientOrigin,
      cost ≤ 200 * (B + remaining.length + 3) * remaining.length + 4 ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 80 ∧
      t.tapes 0 = BitTape.shifted (divideFrom divisor remainder quotient remaining).1 resultOrigin ∧
      t.tapes 1 = BitTape.shifted divisor xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 4 = BitTape.shifted (divideFrom divisor remainder quotient remaining).2 quotientOrigin ∧
      t.tapes 3 = {s.tapes 3 with head := yo - 1} := by
  induction remaining using List.reverseRecOn generalizing remainder quotient B s ao zo qo with
  | nil =>
    refine ⟨4, stoppedState s, ao, zo, qo, by simp, stop_block input tape s hpc h3.nil_read,
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [stoppedState] using h0
    · simpa [stoppedState] using h1
    · simpa [stoppedState] using h2
    · simpa [stoppedState] using h4
    · have hh := h3.head
      simp only [List.length_nil, Nat.cast_zero, add_zero] at hh
      simp [stoppedState, hh]
  | append_singleton remaining b ih =>
    have hf := fetch_block input tape s b hpc h3.last_read
    have hf0 := fetchedState_remainder s b remainder ao h0
    have hf3 := fetchedState_prefix s remaining yo b h3
    obtain ⟨reduceCost, reduced, newOrigin, hc, hs, hp, hb, ht0, ht1, ht2, hframe⟩ :=
      reduceCycle input tape (fetchedState s b) (b :: remainder) divisor (ao - 1) xo zo
        (by simp) hd rfl hf0 (by simpa [fetchedState] using h1)
        (by simpa [fetchedState] using h2)
    have hreduceWidth : (remainderStep divisor remainder b).length ≤ B + 1 :=
      remainderStep_length_le divisor remainder b B hdB hrB
    have hreducePrefix : PrefixTape (reduced.tapes 3) remaining yo := by
      rw [hframe.higher_tapes 3 (by omega)]
      exact hf3
    have hreduceQ : reduced.tapes 4 = BitTape.shifted quotient qo := by
      rw [hframe.higher_tapes 4 (by omega)]
      simpa [fetchedState] using h4
    have he := emit_block input tape reduced hp
    have he4 : (emittedState reduced).tapes 4 =
        BitTape.shifted (quotientBit divisor remainder b :: quotient) (qo - 1) := by
      simpa [hb, quotientBit] using emittedState_quotient reduced quotient qo hreduceQ
    obtain ⟨cost, t, ro, so, qro, hiCost, hiSteps, hiPc, hi0, hi1, hi2, hi4, hi3⟩ :=
      ih (remainderStep divisor remainder b) (quotientBit divisor remainder b :: quotient)
        (B + 1) (emittedState reduced) newOrigin
        (zo + max (b :: remainder).length divisor.length) (qo - 1)
        (by omega) hreduceWidth rfl (by simpa [emittedState, remainderStep] using ht0)
        (by simpa [emittedState] using ht1) (by simpa [emittedState] using ht2)
        (by simpa [emittedState] using hreducePrefix) he4
    refine ⟨6 + reduceCost + 4 + cost, t, ro, so, qro, ?_,
      ((hf.trans hs).trans he).trans hiSteps, hiPc, ?_, hi1, hi2, ?_, ?_⟩
    · have hmax : max (b :: remainder).length divisor.length ≤ B + 1 := by
        simp only [List.length_cons]
        omega
      simp only [List.length_append, List.length_singleton]
      nlinarith
    · simpa [divideFrom_append_bit] using hi0
    · simpa [divideFrom_append_bit] using hi4
    · simpa [emittedState, hframe.higher_tapes 3 (by omega), fetchedState] using hi3

theorem loop_simulation (input : List Bool) (tape : ℕ → Bool)
    (divisor : List Bool) (hd : 0 < divisor.length)
    (remaining remainder quotient : List Bool) (B : ℕ)
    (s : BitRAMState) (ao xo zo yo qo : ℤ)
    (hdB : divisor.length ≤ B) (hrB : remainder.length ≤ B)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = BitTape.shifted remainder ao)
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : PrefixTape (s.tapes 3) remaining yo)
    (h4 : s.tapes 4 = BitTape.shifted quotient qo) :
    ∃ cost t resultOrigin scratchOrigin quotientOrigin,
      cost ≤ 200 * (B + remaining.length + 3) * remaining.length + 4 ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 80 ∧
      t.tapes 0 = BitTape.shifted (divideFrom divisor remainder quotient remaining).1 resultOrigin ∧
      t.tapes 1 = BitTape.shifted divisor xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 4 = BitTape.shifted (divideFrom divisor remainder quotient remaining).2 quotientOrigin := by
  obtain ⟨cost, t, ro, so, qo, hc, hs, hp, ht0, ht1, ht2, ht4, _⟩ :=
    loop_simulation_full input tape divisor hd remaining remainder quotient B s ao xo zo yo qo
      hdB hrB hpc h0 h1 h2 h3 h4
  exact ⟨cost, t, ro, so, qo, hc, hs, hp, ht0, ht1, ht2, ht4⟩

/-- Every positive padded binary divisor is supported, including division of
zero and operands with arbitrary high zero bits. Both results are exact. -/
theorem simulation_cleanup (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (divisor dividend : List Bool) (ao xo zo yo qo : ℤ)
    (hd : 0 < addressValue divisor)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = BitTape.shiftedEnd dividend yo)
    (h4 : s.tapes 4 = {BitTape.blank with head := qo}) :
    ∃ cost t remainder quotient resultOrigin scratchOrigin quotientOrigin,
      cost ≤ 400 * (divisor.length + dividend.length + 2) * (dividend.length + 1) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 80 ∧
      t.tapes 0 = BitTape.shifted remainder resultOrigin ∧
      t.tapes 1 = BitTape.shifted divisor xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 4 = BitTape.shifted quotient quotientOrigin ∧
      addressValue remainder = addressValue dividend % addressValue divisor ∧
      addressValue quotient = addressValue dividend / addressValue divisor ∧
      remainder.length ≤ divisor.length + dividend.length ∧ quotient.length = dividend.length ∧
      t.tapes 3 = {BitTape.shifted dividend yo with head := yo - 1} := by
  have hdlen : 0 < divisor.length := by
    cases divisor with
    | nil => simp [addressValue] at hd
    | cons b bs => simp
  obtain ⟨cost, t, ro, so, qro, hc, hs, hp, ht0, ht1, ht2, ht4, ht3⟩ :=
    loop_simulation_full input tape divisor hdlen dividend [] [] divisor.length s ao xo zo yo qo
      le_rfl (by simp) hpc (by simpa using h0) h1 h2
      (by simpa [h3] using HornerMultiply.PrefixTape.shiftedEnd dividend yo) (by simpa using h4)
  have hvalue := divideFrom_value divisor [] [] dividend hd (by simpa [addressValue] using hd)
  simp only [addressValue, mul_zero, add_zero, zero_add] at hvalue
  have hlength := divideFrom_length_le divisor [] [] dividend divisor.length le_rfl (by simp)
  refine ⟨cost, t, (divideFrom divisor [] [] dividend).1, (divideFrom divisor [] [] dividend).2,
    ro, so, qro, by nlinarith, hs, hp, ht0, ht1, ht2, ht4, ?_, ?_, hlength.1, ?_, ?_⟩
  · rw [← hvalue.2, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hvalue.1]
  · rw [← hvalue.2, Nat.add_comm, Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt hvalue.1]
    simp
  · simpa using hlength.2
  · simpa [h3, BitTape.shiftedEnd] using ht3

theorem simulation (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (divisor dividend : List Bool) (ao xo zo yo qo : ℤ)
    (hd : 0 < addressValue divisor)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = BitTape.shiftedEnd dividend yo)
    (h4 : s.tapes 4 = {BitTape.blank with head := qo}) :
    ∃ cost t remainder quotient resultOrigin scratchOrigin quotientOrigin,
      cost ≤ 400 * (divisor.length + dividend.length + 2) * (dividend.length + 1) ∧
      PricedSteps (program.next input tape) cost s t ∧ t.pc = 80 ∧
      t.tapes 0 = BitTape.shifted remainder resultOrigin ∧
      t.tapes 1 = BitTape.shifted divisor xo ∧
      t.tapes 2 = {BitTape.blank with head := scratchOrigin} ∧
      t.tapes 4 = BitTape.shifted quotient quotientOrigin ∧
      addressValue remainder = addressValue dividend % addressValue divisor ∧
      addressValue quotient = addressValue dividend / addressValue divisor ∧
      remainder.length ≤ divisor.length + dividend.length ∧ quotient.length = dividend.length := by
  obtain ⟨cost, t, remainder, quotient, ro, so, qo, hc, hs, hp, ht0, ht1, ht2, ht4, hr, hq, hlr, hlq, _⟩ :=
    simulation_cleanup input tape s divisor dividend ao xo zo yo qo hd hpc h0 h1 h2 h3 h4
  exact ⟨cost, t, remainder, quotient, ro, so, qo, hc, hs, hp, ht0, ht1, ht2, ht4, hr, hq, hlr, hlq⟩

/-- Capped execution of one fixed Boolean program computes exact quotient and
remainder with a quadratic bound in the input word lengths. -/
theorem run (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (divisor dividend : List Bool) (ao xo zo yo qo : ℤ)
    (hd : 0 < addressValue divisor)
    (hpc : s.pc = 0) (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted divisor xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.tapes 3 = BitTape.shiftedEnd dividend yo)
    (h4 : s.tapes 4 = {BitTape.blank with head := qo}) :
    ∃ t remainder quotient resultOrigin quotientOrigin,
      (runPriced (program.next input tape)
        (400 * (divisor.length + dividend.length + 2) * (dividend.length + 1) + 1) s).finished = some t ∧
      (runPriced (program.next input tape)
        (400 * (divisor.length + dividend.length + 2) * (dividend.length + 1) + 1) s).instructions ≤
          400 * (divisor.length + dividend.length + 2) * (dividend.length + 1) ∧
      t.tapes 0 = BitTape.shifted remainder resultOrigin ∧
      t.tapes 4 = BitTape.shifted quotient quotientOrigin ∧
      addressValue remainder = addressValue dividend % addressValue divisor ∧
      addressValue quotient = addressValue dividend / addressValue divisor ∧
      remainder.length ≤ divisor.length + dividend.length ∧ quotient.length = dividend.length := by
  obtain ⟨cost, t, remainder, quotient, ro, so, qro, hc, hs, hp, ht0, _, _, ht4, hr, hq, hlr, hlq⟩ :=
    simulation input tape s divisor dividend ao xo zo yo qo hd hpc h0 h1 h2 h3 h4
  have halt : program.next input tape t = none := by
    simp [BitRAM.next, program, hp, Subtraction.program, RewindOvershoot.program,
      RewindOvershoot.preamble, BitRAM.link, Rewind.program, TapeOps.clear,
      TapeOps.copyClear, BitRAMInstruction.relocate]
  have hrun := hs.runPriced_ge halt
    (400 * (divisor.length + dividend.length + 2) * (dividend.length + 1) + 1) (by omega)
  exact ⟨t, remainder, quotient, ro, qro, hrun.1, by simpa [hrun.2] using hc,
    ht0, ht4, hr, hq, hlr, hlq⟩

end Maxwell.Cost.Division
