import Maxwell.Cost.DyadicSqrt.Loop
import Maxwell.Cost.WordCall

/-! A fixed Boolean square-root machine. The output is an unreduced dyadic
rational represented by two actual integer words. -/

namespace Maxwell.Cost.DyadicSqrt

open Structured RationalAccumulator
open Maxwell.Defect.DyadicSqrt.Integer

def upperCode : Code := .seq loopCode
  (.seq (addCode 34 32) (.call (TapeOps.clear 40)))

def upperBudget (A B p : ℕ) : ℕ := loopBudget A B p + 230 * (p + 5) + 6 * p.bits.length + 4

theorem cycleBudget_le_polynomial (W : ℕ) :
    cycleBudget W ≤ 14000000000 * (W + 4)^2 := by
  have hsq : W + 4 ≤ (W + 4)^2 := Nat.le_self_pow (by decide) _
  unfold cycleBudget
  rw [mul_pow]
  norm_num
  omega

theorem upperBudget_le_polynomial (A B p : ℕ) :
    upperBudget A B p ≤
      (p + 1) * (14000000000 * (A.bits.length + B.bits.length + 2*p + 5)^2 + 250*(p+5)) := by
  have hcycle := cycleBudget_le_polynomial (A.bits.length + B.bits.length + 2 * p + 1)
  have hp : p.bits.length ≤ p := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := p))
  have hcycle' : p * cycleBudget (A.bits.length + B.bits.length + 2*p+1) ≤
      (p+1) * (14000000000 * (A.bits.length + B.bits.length + 2*p+5)^2) := by
    apply Nat.mul_le_mul (by omega)
    convert hcycle using 1
  unfold upperBudget loopBudget
  nlinarith

theorem increment_bank_value (A B L P : ℕ) :
    Function.update (bank A B L P) 32 ((bank A B L P) 34 + (bank A B L P) 32) =
      bank A B (L + 1) P := by
  funext i
  by_cases hi : i = 32
  · subst i; simp [bank, Nat.add_comm]
  · simp [bank, hi]

/-- The upper square-root endpoint is computed from the same integer
bisection, and its private precision counter is erased before return. -/
theorem upper_executes (input : List Bool) (tape : ℕ → Bool) (A B p : ℕ)
    (origin : ℤ) (s : Store)
    (hbank : Bank s.val (bank A B 0 1)) (hready : Scratch s.val 0)
    (hcounter : s.val.tapes 40 = BitTape.shifted p.bits origin) :
    ∃ cost, ∃ t : Store, cost ≤ upperBudget A B p ∧
      Executes input tape upperCode cost s t ∧
      Bank t.val (bank (A * 4^p) B (lowerNum A B p + 1) (2^p)) ∧
      Scratch t.val 0 ∧ Blank t.val 40 ∧ LoopFrame s.val t.val := by
  obtain ⟨cost, a, counter, hc, ea, ba, ra, haCounter, haLength, fa⟩ :=
    loop_executes input tape A B p origin s hbank hready hcounter
  obtain ⟨addCost, b, hbc, eb, bb, rb, fb⟩ := add 34 32 (by decide) (by decide)
    (by decide) (by decide) input tape (bank (A * 4^p) B (lowerNum A B p) (2^p)) a ba ra
  have hAdd : addCost ≤ 230 * (p + 5) := by
    have hl := lowerNum_bits_length_le A B p
    change addCost ≤ 230 * ((1 : ℕ).bits.length + (lowerNum A B p).bits.length + 4) at hbc
    rw [show (1 : ℕ).bits.length = 1 from rfl] at hbc
    omega
  rw [increment_bank_value] at bb
  have hbCounter : b.val.tapes 40 = BitTape.shifted counter origin :=
    (fb.2.2.2.2.2.1 40 (by decide) (by decide)).trans haCounter
  obtain ⟨t, et, htapes, ft⟩ := WordCall.clear 40 input tape counter origin b hbCounter
  have fclear : LoopFrame b.val t.val := by
    rcases ft with ⟨ha, hi, hm, hr, ho, ht, hg⟩
    exact ⟨ha, hi, hm, hr, ho, fun i hi => ht i (by omega) (by omega),
      fun i hi => hg i (by omega) (by omega)⟩
  refine ⟨cost + (addCost + (6 * counter.length + 4)), t, by unfold upperBudget; omega,
    ea.seq (eb.seq et), ?_, ?_, ⟨origin + counter.length, by simp [htapes]⟩,
    (fa.trans (LoopFrame.of_cycle (frame_of_bank fb))).trans fclear⟩
  · intro i hi hi'
    exact word_of_eq (ft.2.2.2.2.2.1 i (by omega) (by omega)) (bb i hi hi')
  · exact ⟨blank_of_eq (ft.2.2.2.2.2.1 0 (by decide) (by decide)) rb.1,
      word_of_eq (ft.2.2.2.2.2.1 1 (by decide) (by decide)) rb.2.1,
      blank_of_eq (ft.2.2.2.2.2.1 2 (by decide) (by decide)) rb.2.2.1,
      blank_of_eq (ft.2.2.2.2.2.1 3 (by decide) (by decide)) rb.2.2.2⟩

/-- Capped execution returns the proved actual dyadic upper endpoint.
Both numerator and denominator are produced by the compiled machine. -/
theorem upper_run (input : List Bool) (tape : ℕ → Bool) (A B p : ℕ) (hB : 0 < B)
    (origin : ℤ) (s : Store)
    (hbank : Bank s.val (bank A B 0 1)) (hready : Scratch s.val 0)
    (hcounter : s.val.tapes 40 = BitTape.shifted p.bits origin) :
    ∃ t : Store,
      (runPriced (upperCode.compile.next input tape) (upperBudget A B p + 1) s.val).finished =
        some (t.place upperCode.size) ∧
      (runPriced (upperCode.compile.next input tape) (upperBudget A B p + 1) s.val).instructions ≤
        upperBudget A B p ∧
      Word t.val 32 (lowerNum A B p + 1) ∧ Word t.val 33 (2^p) ∧
      ((lowerNum A B p + 1 : ℕ) : ℚ) / (2^p : ℕ) =
        Maxwell.Defect.DyadicSqrt.upper ((A : ℚ) / B) p ∧
      Scratch t.val 0 ∧ Blank t.val 40 ∧ LoopFrame s.val t.val := by
  obtain ⟨cost, t, hc, he, hb, hr, hblank, hf⟩ :=
    upper_executes input tape A B p origin s hbank hready hcounter
  have run := he.compiled_run (upperBudget A B p + 1) (by omega)
  exact ⟨t, run.1, run.2 ▸ hc, by simpa [bank] using hb 32 (by decide) (by decide),
    by simpa [bank] using hb 33 (by decide) (by decide),
    by simpa using upper_binding A B p hB, hr, hblank, hf⟩

end Maxwell.Cost.DyadicSqrt
