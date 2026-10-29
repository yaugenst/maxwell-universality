import Maxwell.Cost.RealRound
import Maxwell.Cost.RealLink
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size

/-! Midpoint rounding produces already reduced dyadic rationals: every
nonzero result has odd numerator and a power-of-two denominator. The exact
zero branch preserves sparse zeros. All values come from actual charged
comparisons and arithmetic of the finite digit program. -/
namespace Maxwell.Cost.RealMidpoint
open RealSparse (execute execute_sound execute_add)
open RealRound (input digitState Ready preinitialized initialized doubled advanced
  initialized_ready advanced_ready)
set_option maxRecDepth 20000

noncomputable def magnitude (x : ℝ) (p : ℕ) : ℕ :=
  if x = 0 then 0 else 2 * (digitState x p).1 + 1

noncomputable def denominator (x : ℝ) (p : ℕ) : ℕ :=
  if x = 0 then 1 else 2 ^ (p + 1)

noncomputable def numerator (x : ℝ) (p : ℕ) : ℤ :=
  if 0 ≤ x then (magnitude x p : ℤ) else -(magnitude x p : ℤ)

noncomputable def approximation (x : ℝ) (p : ℕ) : ℚ :=
  (numerator x p : ℚ) / denominator x p

/-- The first 35 instructions are the existing binary digit loop. -/
def program : Machine := ⟨RealRound.program.code.take 35 ++ [
  .branchLE 0 7 36 42, .branchLE 7 0 37 42,
  .literal 4 0, .indexLiteral 4 0, .indexLiteral 5 1, .jump 52, .halt,
  .multiply 4 4 2, .add 4 4 6, .multiply 5 5 2, .divide 4 4 5,
  .indexAdd 4 4 4, .indexAdd 4 4 1, .indexAdd 5 5 5,
  .branchLE 7 0 52 50, .multiply 4 4 3, .jump 52,
  .output 4, .outputIndex 4, .outputIndex 5, .halt]⟩

set_option maxHeartbeats 1400000 in
theorem initialize_steps (x : ℝ) (p : ℕ) (tape : ℕ → Bool) :
    execute (program.next (input x p) tape) 16 RAMState.initial = some (initialized x p) := by
  have hprefix : execute (program.next (input x p) tape) 12 RAMState.initial = some (preinitialized x p) := by
    simp [execute, program, RealRound.program, Machine.next, preinitialized, input, RAMState.initial, RAMState.setWord, RAMState.setIndex]
  rw [show 16 = 12 + 4 from rfl, execute_add, hprefix, Option.bind_some]
  by_cases hx : 0 ≤ x
  · simp [execute, program, RealRound.program, Machine.next, initialized, preinitialized, RAMState.initial,
      RAMState.setWord, RAMState.setIndex, hx, abs_of_nonneg hx]
  · simp [execute, program, RealRound.program, Machine.next, initialized, preinitialized, RAMState.initial,
      RAMState.setWord, RAMState.setIndex, hx, abs_of_neg (lt_of_not_ge hx)]

set_option maxHeartbeats 1400000 in
theorem cycle (x : ℝ) (p k : ℕ) (tape : ℕ → Bool) (s : RAMState)
    (h : Ready s x p k) (hk : k < p) :
    execute (program.next (input x p) tape) 13 s = some (advanced s) := by
  rcases h with ⟨hpc, h1, hp, hi, _, _, _, _, h2, hm, _, _, hw, _, _, _, _⟩
  have hnot : ¬ p ≤ k := by omega
  have hf : execute (program.next (input x p) tape) 6 s = some (doubled s) := by
    simp [execute, program, RealRound.program, Machine.next, hpc, hp, hi, h2, hnot, doubled, RAMState.setWord, RAMState.setIndex]
  rw [show 13 = 6 + 7 from rfl, execute_add, hf, Option.bind_some]
  by_cases hd : 1 ≤ s.words 1 * 2
  · simp [execute, program, RealRound.program, Machine.next, doubled, advanced, h1, hi, hm, hw, hd,
      RAMState.setWord, RAMState.setIndex, sub_eq_add_neg]
  · simp [execute, program, RealRound.program, Machine.next, doubled, advanced, h1, hi, hw, hd,
      RAMState.setWord, RAMState.setIndex]

theorem scan (x : ℝ) (p : ℕ) (tape : ℕ → Bool) (remaining : ℕ) (s : RAMState) (k : ℕ)
    (h : Ready s x p k) (hcount : k + remaining = p) :
    ∃ final : RAMState, Steps (program.next (input x p) tape) (13 * remaining) s final ∧ Ready final x p p := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = p := by omega
    subst k
    exact ⟨s, Steps.refl s, h⟩
  | succ remaining ih =>
    have hk : k < p := by omega
    obtain ⟨f, hf, hfr⟩ := ih (advanced s) (k + 1) (advanced_ready x p k s h) (by omega)
    refine ⟨f, ?_, hfr⟩
    convert (execute_sound _ (cycle x p k tape s h hk)).trans hf using 1
    omega


noncomputable def finishCost (x : ℝ) : ℕ :=
  if x = 0 then 10 else if 0 ≤ x then 13 else 16

noncomputable def arithmetic (s : RAMState) : RAMState :=
  let t := ({s with pc := 42} : RAMState).setWord 4 (s.words 4 * 2)
  let t := t.setWord 4 (s.words 4 * 2 + 1)
  let t := t.setWord 5 (s.words 5 * 2)
  let t := t.setWord 4 ((s.words 4 * 2 + 1) / (s.words 5 * 2))
  let t := t.setIndex 4 (s.indices 4 + s.indices 4)
  let t := t.setIndex 4 (s.indices 4 + s.indices 4 + 1)
  t.setIndex 5 (s.indices 5 + s.indices 5)

noncomputable def finished (s : RAMState) (x : ℝ) (p : ℕ) : RAMState :=
  let t := if x = 0 then
      ((({s with pc := 37} : RAMState).setWord 4 0).setIndex 4 0).setIndex 5 1
    else if 0 ≤ x then arithmetic s
    else (arithmetic s).setWord 4 (-((s.words 4 * 2 + 1) / (s.words 5 * 2)))
  {t with pc := 55, output := (approximation x p : ℝ) :: s.output, indexOutput := denominator x p :: magnitude x p :: s.indexOutput}

set_option maxHeartbeats 1600000 in
theorem finish_steps (x : ℝ) (p : ℕ) (tape : ℕ → Bool) (s : RAMState)
    (h : Ready s x p p) :
    execute (program.next (input x p) tape) (finishCost x) s = some (finished s x p) := by
  rcases h with ⟨hpc, h1, hp, hi, hn, hd, hx, _, h2, hm, hnR, hdR, hw, hz, _, _, _⟩
  by_cases hx0 : x = 0
  · rcases hx0 with rfl
    simp [execute, program, RealRound.program, Machine.next, finishCost, finished,
      approximation, numerator, magnitude, denominator, hpc, hp, hi, hx, hz,
      RAMState.setWord, RAMState.setIndex]
  · have ha : execute (program.next (input x p) tape) 7 {s with pc := 42} = some (arithmetic s) := by
      simp [execute, program, RealRound.program, Machine.next, arithmetic, h1, h2, hw,
        RAMState.setWord, RAMState.setIndex]
    by_cases hxpos : 0 ≤ x
    · have hxneg : ¬ x ≤ 0 := by
        intro hn
        exact hx0 (le_antisymm hn hxpos)
      have hf : execute (program.next (input x p) tape) 2 s = some {s with pc := 42} := by
        simp [execute, program, RealRound.program, Machine.next, hpc, hp, hi, hx, hz, hxneg]
      rw [show finishCost x = 2 + (7 + 4) by simp [finishCost, hx0, hxpos], execute_add, hf,
        Option.bind_some, execute_add, ha, Option.bind_some]
      simp [execute, program, RealRound.program, Machine.next, finished, arithmetic,
        approximation, numerator, magnitude, denominator, hx0, hxpos,
        hn, hd, hx, hnR, hdR, hz, RAMState.setWord, RAMState.setIndex, pow_succ, two_mul]
      constructor <;> ring
    · have hxneg : x ≤ 0 := le_of_not_ge hxpos
      have hf : execute (program.next (input x p) tape) 3 s = some {s with pc := 42} := by
        simp [execute, program, RealRound.program, Machine.next, hpc, hp, hi, hx, hz, hxneg, hxpos]
      rw [show finishCost x = 3 + (7 + 6) by simp [finishCost, hx0, hxpos], execute_add, hf,
        Option.bind_some, execute_add, ha, Option.bind_some]
      simp [execute, program, RealRound.program, Machine.next, finished, arithmetic,
        approximation, numerator, magnitude, denominator, hx0, hxpos,
        hn, hd, hx, hm, hnR, hdR, hz, RAMState.setWord, RAMState.setIndex, pow_succ, two_mul]
      constructor <;> ring

@[simp] theorem magnitude_zero (p : ℕ) : magnitude 0 p = 0 := by simp [magnitude]
@[simp] theorem denominator_zero (p : ℕ) : denominator 0 p = 1 := by simp [denominator]
@[simp] theorem numerator_zero (p : ℕ) : numerator 0 p = 0 := by simp [numerator]
@[simp] theorem approximation_zero (p : ℕ) : approximation 0 p = 0 := by simp [approximation]

theorem denominator_pos (x : ℝ) (p : ℕ) : 0 < denominator x p := by
  unfold denominator
  split_ifs <;> positivity

theorem numerator_natAbs (x : ℝ) (p : ℕ) : (numerator x p).natAbs = magnitude x p := by
  unfold numerator
  split_ifs <;> simp

theorem magnitude_lt (x : ℝ) (p : ℕ) : magnitude x p < 2 ^ (p + 1) := by
  have h := RealRound.numerator_lt x p
  unfold magnitude
  split_ifs <;> rw [pow_succ] <;> omega

theorem numerator_denominator_coprime (x : ℝ) (p : ℕ) :
    (numerator x p).natAbs.Coprime (denominator x p) := by
  rw [numerator_natAbs]
  by_cases hx : x = 0
  · simp [magnitude, denominator, hx]
  · simp only [magnitude, denominator, hx, ↓reduceIte]
    exact (Nat.coprime_two_right.mpr ⟨(digitState x p).1, by omega⟩).pow_right (p + 1)

/-- No hidden gcd computation occurs when the machine emits this pair. -/
theorem approximation_num (x : ℝ) (p : ℕ) : (approximation x p).num = numerator x p := by
  exact Rat.num_div_eq_of_coprime (a := numerator x p) (b := (denominator x p : ℤ))
    (by exact_mod_cast denominator_pos x p)
    (by simpa using numerator_denominator_coprime x p)

theorem approximation_den (x : ℝ) (p : ℕ) : (approximation x p).den = denominator x p := by
  have h := Rat.den_div_eq_of_coprime (a := numerator x p) (b := (denominator x p : ℤ))
    (by exact_mod_cast denominator_pos x p)
    (by simpa using numerator_denominator_coprime x p)
  unfold approximation
  exact_mod_cast h

/-- Midpoints have half the mesh width of the underlying digit loop. -/
theorem approximation_error (x : ℝ) (p : ℕ) (hx : |x| ≤ 1) :
    |(approximation x p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ (p + 1) := by
  by_cases hz : x = 0
  · subst x
    simp only [approximation_zero, Rat.cast_zero, sub_self, abs_zero]
    positivity
  have hd : 0 < (2 : ℝ) ^ p := by positivity
  have hr := RealRound.remainder_bounds x p hx
  have hi := RealRound.digitState_identity x p
  have he : (2 * ((digitState x p).1 : ℝ) + 1) / (2 : ℝ) ^ (p + 1) - |x| =
      (1 - 2 * (digitState x p).2) / (2 : ℝ) ^ (p + 1) := by
    rw [pow_succ]
    field_simp
    nlinarith [hi]
  have hb : |1 - 2 * (digitState x p).2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hr.1, hr.2]
  have hb' : |(1 - 2 * (digitState x p).2) / (2 : ℝ) ^ (p + 1)| ≤
      1 / (2 : ℝ) ^ (p + 1) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ (p + 1))]
    exact div_le_div_of_nonneg_right hb (by positivity)
  by_cases hs : 0 ≤ x
  · rw [abs_of_nonneg hs] at he
    simpa [approximation, numerator, magnitude, denominator, hz, hs, he] using hb'
  · have hn : x < 0 := lt_of_not_ge hs
    rw [abs_of_neg hn] at he
    have he' : -(2 * ((digitState x p).1 : ℝ) + 1) / (2 : ℝ) ^ (p + 1) - x =
        -((1 - 2 * (digitState x p).2) / (2 : ℝ) ^ (p + 1)) := by
      simp only [neg_div] at he ⊢
      linarith
    change |(approximation x p : ℝ) - x| ≤ _
    have hcast : (approximation x p : ℝ) =
        -(2 * ((digitState x p).1 : ℝ) + 1) / (2 : ℝ) ^ (p + 1) := by
      simp [approximation, numerator, magnitude, denominator, hz, hs]
    rw [hcast, he', abs_neg]
    exact hb'

theorem finishCost_le (x : ℝ) : finishCost x ≤ 16 := by
  unfold finishCost
  split_ifs <;> omega

/-- The actual emitted pair is the canonical rational pair. -/
theorem terminates (x : ℝ) (p : ℕ) (tape : ℕ → Bool) :
    ∃ cost : ℕ, ∃ final : RAMState,
      cost ≤ 13 * p + 32 ∧
      Terminates (program.next (input x p) tape) cost RAMState.initial final ∧
      final.output = [(approximation x p : ℝ)] ∧
      final.indexOutput.reverse = [(approximation x p).num.natAbs, (approximation x p).den] ∧
      final.randomCursor = 0 := by
  have hi := execute_sound _ (initialize_steps x p tape)
  obtain ⟨s, hs, hsr⟩ := scan x p tape p (initialized x p) 0 (initialized_ready x p) (by omega)
  have hf := execute_sound _ (finish_steps x p tape s hsr)
  have ho : s.output = [] := hsr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hio : s.indexOutput = [] := hsr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc : s.randomCursor = 0 := hsr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨16 + 13 * p + finishCost x, finished s x p, by have := finishCost_le x; omega,
    ?_, ?_, ?_, ?_⟩
  · exact ((hi.trans hs).trans hf).terminates
      (Terminates.halt _ (by simp [program, RealRound.program, Machine.next, finished]))
  · simp [finished, ho]
  · simp [finished, hio, approximation_num, approximation_den, numerator_natAbs]
  · simp only [finished]
    split_ifs <;> simp [arithmetic, RAMState.setIndex, RAMState.setWord, hc]

theorem run (x : ℝ) (p : ℕ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      (program.run (input x p) tape (13 * p + 33)).finished = some final ∧
      (program.run (input x p) tape (13 * p + 33)).instructions ≤ 13 * p + 32 ∧
      final.output = [(approximation x p : ℝ)] ∧
      final.indexOutput.reverse = [(approximation x p).num.natAbs, (approximation x p).den] := by
  obtain ⟨cost, t, hc, ht, ho, hi, _⟩ := terminates x p tape
  obtain ⟨hf, hcost⟩ := runCapped_of_terminates_ge _ ht (13 * p + 33) (by omega)
  exact ⟨t, hf, hcost.le.trans hc, ho, hi⟩

theorem approximation_eq_zero_iff (x : ℝ) (p : ℕ) : approximation x p = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hn := congrArg (fun q : ℚ => q.num.natAbs) h
    rw [approximation_num, numerator_natAbs] at hn
    by_contra hx
    simp [magnitude, hx] at hn
  · rintro rfl
    exact approximation_zero p

theorem numerator_bits_le (x : ℝ) (p : ℕ) : (approximation x p).num.natAbs.bits.length ≤ p + 1 := by
  rw [approximation_num, numerator_natAbs, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (magnitude_lt x p)

theorem denominator_bits_le (x : ℝ) (p : ℕ) : (approximation x p).den.bits.length ≤ p + 2 := by
  rw [approximation_den, Nat.size_eq_bits_len]
  unfold denominator
  split_ifs <;> simp [Nat.size_pow]

end Maxwell.Cost.RealMidpoint
