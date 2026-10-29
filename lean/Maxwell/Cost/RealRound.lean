import Maxwell.Cost.RealNormalize

/-! Dyadic approximation of arbitrary real inputs in [-1,1] by a fixed
finite program. Each binary decision uses a comparison of real words.
The machine also computes the natural numerator and denominator, ready
for a separately charged canonical binary encoding. -/

namespace Maxwell.Cost.RealRound

open RealSparse (execute execute_sound execute_add)
set_option maxRecDepth 20000

noncomputable def digitState (x : ℝ) : ℕ → ℕ × ℝ
  | 0 => (0, |x|)
  | k + 1 =>
      let s := digitState x k
      if 1 ≤ 2 * s.2 then (2 * s.1 + 1, 2 * s.2 - 1) else (2 * s.1, 2 * s.2)

noncomputable def approximation (x : ℝ) (p : ℕ) : ℚ :=
  if 0 ≤ x then ((digitState x p).1 : ℚ) / 2 ^ p else -((digitState x p).1 : ℚ) / 2 ^ p

noncomputable def input (x : ℝ) (p : ℕ) : RAMInput :=
  ⟨fun _ => x, fun a => if a = 0 then p else 0⟩

/-- Forty-five instructions; the branch paths have equal costs. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .inputIndex 2 0,
  .indexLiteral 3 0, .indexLiteral 4 0, .indexLiteral 5 1,
  .input 0 0, .literal 2 2, .literal 3 (-1), .literal 4 0,
  .literal 5 1, .literal 6 1, .literal 7 0,
  .branchLE 7 0 14 16, .copy 1 0, .jump 18, .multiply 1 0 3, .jump 18,
  .branchIndexLE 2 3 35 19,
  .multiply 1 1 2, .multiply 4 4 2, .multiply 5 5 2,
  .indexAdd 4 4 4, .indexAdd 5 5 5,
  .branchLE 6 1 25 29,
  .add 1 1 3, .add 4 4 6, .indexAdd 4 4 1, .jump 33,
  .copy 1 1, .copy 4 4, .indexCopy 4 4, .jump 33,
  .indexAdd 3 3 1, .jump 18,
  .divide 4 4 5, .branchLE 7 0 37 39,
  .copy 4 4, .jump 41, .multiply 4 4 3, .jump 41,
  .output 4, .outputIndex 4, .outputIndex 5, .halt]⟩

def Ready (s : RAMState) (x : ℝ) (p k : ℕ) : Prop :=
  s.pc = 18 ∧ s.indices 1 = 1 ∧ s.indices 2 = p ∧ s.indices 3 = k ∧
    s.indices 4 = (digitState x k).1 ∧ s.indices 5 = 2 ^ k ∧
    s.words 0 = x ∧ s.words 1 = (digitState x k).2 ∧ s.words 2 = 2 ∧ s.words 3 = -1 ∧
    s.words 4 = ((digitState x k).1 : ℝ) ∧ s.words 5 = (2 : ℝ) ^ k ∧
    s.words 6 = 1 ∧ s.words 7 = 0 ∧ s.output = [] ∧ s.indexOutput = [] ∧ s.randomCursor = 0

noncomputable def preinitialized (x : ℝ) (p : ℕ) : RAMState :=
  let s := RAMState.initial.setIndex 0 0
  let s := s.setIndex 1 1
  let s := s.setIndex 2 p
  let s := s.setIndex 3 0
  let s := s.setIndex 4 0
  let s := s.setIndex 5 1
  let s := s.setWord 0 x
  let s := s.setWord 2 2
  let s := s.setWord 3 (-1)
  let s := s.setWord 4 0
  let s := s.setWord 5 1
  s.setWord 6 1

noncomputable def initialized (x : ℝ) (p : ℕ) : RAMState :=
  let s := (preinitialized x p).setWord 7 0
  let s := s.setWord 1 |x|
  {s with pc := 18}

set_option maxHeartbeats 1400000 in
theorem initialize_steps (x : ℝ) (p : ℕ) (tape : ℕ → Bool) :
    execute (program.next (input x p) tape) 16 RAMState.initial = some (initialized x p) := by
  have hprefix : execute (program.next (input x p) tape) 12 RAMState.initial = some (preinitialized x p) := by
    simp [execute, program, Machine.next, preinitialized, input, RAMState.initial, RAMState.setWord, RAMState.setIndex]
  rw [show 16 = 12 + 4 from rfl, execute_add, hprefix, Option.bind_some]
  by_cases hx : 0 ≤ x
  · simp [execute, program, Machine.next, initialized, preinitialized, RAMState.initial,
      RAMState.setWord, RAMState.setIndex, hx, abs_of_nonneg hx]
  · simp [execute, program, Machine.next, initialized, preinitialized, RAMState.initial,
      RAMState.setWord, RAMState.setIndex, hx, abs_of_neg (lt_of_not_ge hx)]

theorem initialized_ready (x : ℝ) (p : ℕ) : Ready (initialized x p) x p 0 := by
  simp [Ready, initialized, preinitialized, digitState, RAMState.initial, RAMState.setWord, RAMState.setIndex]

noncomputable def doubled (s : RAMState) : RAMState :=
  let t := {s with pc := 19}
  let t := t.setWord 1 (s.words 1 * 2)
  let t := t.setWord 4 (s.words 4 * 2)
  let t := t.setWord 5 (s.words 5 * 2)
  let t := t.setIndex 4 (s.indices 4 + s.indices 4)
  t.setIndex 5 (s.indices 5 + s.indices 5)

noncomputable def advanced (s : RAMState) : RAMState :=
  let t := doubled s
  let t := if 1 ≤ s.words 1 * 2 then
      ((t.setWord 1 (s.words 1 * 2 - 1)).setWord 4 (s.words 4 * 2 + 1)).setIndex 4 (s.indices 4 + s.indices 4 + 1)
    else ((t.setWord 1 (s.words 1 * 2)).setWord 4 (s.words 4 * 2)).setIndex 4 (s.indices 4 + s.indices 4)
  let t := t.setIndex 3 (s.indices 3 + 1)
  {t with pc := 18}

set_option maxHeartbeats 1400000 in
theorem cycle (x : ℝ) (p k : ℕ) (tape : ℕ → Bool) (s : RAMState)
    (h : Ready s x p k) (hk : k < p) :
    execute (program.next (input x p) tape) 13 s = some (advanced s) := by
  rcases h with ⟨hpc, h1, hp, hi, _, _, _, _, h2, hm, _, _, hw, _, _, _, _⟩
  have hnot : ¬ p ≤ k := by omega
  have hf : execute (program.next (input x p) tape) 6 s = some (doubled s) := by
    simp [execute, program, Machine.next, hpc, hp, hi, h2, hnot, doubled, RAMState.setWord, RAMState.setIndex]
  rw [show 13 = 6 + 7 from rfl, execute_add, hf, Option.bind_some]
  by_cases hd : 1 ≤ s.words 1 * 2
  · simp [execute, program, Machine.next, doubled, advanced, h1, hi, hm, hw, hd,
      RAMState.setWord, RAMState.setIndex, sub_eq_add_neg]
  · simp [execute, program, Machine.next, doubled, advanced, h1, hi, hw, hd,
      RAMState.setWord, RAMState.setIndex]

theorem advanced_ready (x : ℝ) (p k : ℕ) (s : RAMState) (h : Ready s x p k) :
    Ready (advanced s) x p (k + 1) := by
  rcases h with ⟨_, h1, hp, hi, hnum, hden, hx, hr, h2, hm, hnR, hdR, hw, hz, ho, hio, hc⟩
  by_cases hd : 1 ≤ 2 * (digitState x k).2
  · simp only [two_mul] at hd
    simp [Ready, advanced, doubled, digitState, RAMState.setWord, RAMState.setIndex,
      h1, hp, hi, hnum, hden, hx, hr, h2, hm, hnR, hdR, hw, hz, ho, hio, hc, hd,
      mul_comm, two_mul, pow_succ]
  · simp only [two_mul] at hd
    simp [Ready, advanced, doubled, digitState, RAMState.setWord, RAMState.setIndex,
      h1, hp, hi, hnum, hden, hx, hr, h2, hm, hnR, hdR, hw, hz, ho, hio, hc, hd,
      mul_comm, two_mul, pow_succ]

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

noncomputable def finished (s : RAMState) (x : ℝ) (p : ℕ) : RAMState :=
  let t := s.setWord 4 (approximation x p : ℝ)
  {t with pc := 44, output := (approximation x p : ℝ) :: s.output, indexOutput := 2 ^ p :: (digitState x p).1 :: s.indexOutput}

set_option maxHeartbeats 1400000 in
theorem finish_steps (x : ℝ) (p : ℕ) (tape : ℕ → Bool) (s : RAMState) (h : Ready s x p p) :
    execute (program.next (input x p) tape) 8 s = some (finished s x p) := by
  rcases h with ⟨hpc, _, hp, hi, hn, hd, hx, _, _, hm, hnR, hdR, _, hz, _, _, _⟩
  by_cases hx0 : 0 ≤ x
  · simp [execute, program, Machine.next, finished, approximation, hx0, hpc, hp, hi, hn, hd, hx, hnR, hdR, hz,
      RAMState.setWord]
  · simp [execute, program, Machine.next, finished, approximation, hx0, hpc, hp, hi, hn, hd, hx, hm, hnR, hdR, hz,
      RAMState.setWord, neg_div]

theorem terminates (x : ℝ) (p : ℕ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      Terminates (program.next (input x p) tape) (13 * p + 24) RAMState.initial final ∧
      final.output = [(approximation x p : ℝ)] ∧
      final.indexOutput.reverse = [(digitState x p).1, 2 ^ p] ∧ final.randomCursor = 0 := by
  have hi := execute_sound _ (initialize_steps x p tape)
  obtain ⟨s, hs, hsr⟩ := scan x p tape p (initialized x p) 0 (initialized_ready x p) (by omega)
  have hf := execute_sound _ (finish_steps x p tape s hsr)
  refine ⟨finished s x p, ?_, ?_, ?_, hsr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · convert ((hi.trans hs).trans hf).terminates
      (Terminates.halt _ (by simp [program, Machine.next, finished])) using 1
    omega
  · change _ :: s.output = _
    rw [hsr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  · change (_ :: _ :: s.indexOutput).reverse = _
    rw [hsr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl

theorem run (x : ℝ) (p : ℕ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      (program.run (input x p) tape (13 * p + 25)).finished = some final ∧
      (program.run (input x p) tape (13 * p + 25)).instructions = 13 * p + 24 ∧
      final.output = [(approximation x p : ℝ)] ∧
      final.indexOutput.reverse = [(digitState x p).1, 2 ^ p] := by
  obtain ⟨f, ht, ho, hi, _⟩ := terminates x p tape
  obtain ⟨hf, hc⟩ := runCapped_of_terminates _ ht
  exact ⟨f, hf, hc, ho, hi⟩

/-- The comparison loop retains a remainder in the closed unit interval. -/
theorem remainder_bounds (x : ℝ) (p : ℕ) (hx : |x| ≤ 1) :
    0 ≤ (digitState x p).2 ∧ (digitState x p).2 ≤ 1 := by
  induction p with
  | zero => exact ⟨abs_nonneg x, hx⟩
  | succ p ih =>
    simp only [digitState]
    split_ifs with h
    · dsimp
      constructor <;> linarith [ih.2]
    · dsimp
      constructor <;> linarith [ih.1]

/-- Exact radix invariant, including both endpoint values ±1. -/
theorem digitState_identity (x : ℝ) (p : ℕ) :
    ((digitState x p).1 : ℝ) + (digitState x p).2 = (2 : ℝ) ^ p * |x| := by
  induction p with
  | zero => simp [digitState]
  | succ p ih =>
    simp only [digitState]
    split_ifs <;> dsimp <;> push_cast <;> rw [pow_succ] <;> nlinarith [ih]

/-- A p-digit numerator always fits in p bits, even at an endpoint. -/
theorem numerator_lt (x : ℝ) (p : ℕ) : (digitState x p).1 < 2 ^ p := by
  induction p with
  | zero => simp [digitState]
  | succ p ih =>
    simp only [digitState]
    split_ifs <;> dsimp <;> rw [pow_succ] <;> omega

theorem digitState_zero (p : ℕ) : digitState 0 p = (0, 0) := by
  induction p with
  | zero => simp [digitState]
  | succ p ih => simp [digitState, ih]

@[simp] theorem approximation_zero (p : ℕ) : approximation 0 p = 0 := by
  simp [approximation, digitState_zero]

/-- The generated rational is within one dyadic mesh width of the input. -/
theorem approximation_error (x : ℝ) (p : ℕ) (hx : |x| ≤ 1) :
    |(approximation x p : ℝ) - x| ≤ 1 / (2 : ℝ) ^ p := by
  have hd : 0 < (2 : ℝ) ^ p := by positivity
  have hr := remainder_bounds x p hx
  have hi := digitState_identity x p
  have he : ((digitState x p).1 : ℝ) / (2 : ℝ) ^ p - |x| =
      -(digitState x p).2 / (2 : ℝ) ^ p := by
    field_simp
    nlinarith [hi]
  by_cases hs : 0 ≤ x
  · simp only [approximation, ite_eq_left hs, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat]
    rw [abs_of_nonneg hs] at he
    rw [he, abs_div, abs_neg, abs_of_nonneg hr.1, abs_of_pos hd]
    exact div_le_div_of_nonneg_right hr.2 hd.le
  · have hn : x < 0 := lt_of_not_ge hs
    have he' : -((digitState x p).1 : ℝ) / (2 : ℝ) ^ p - x =
        (digitState x p).2 / (2 : ℝ) ^ p := by
      rw [abs_of_neg hn] at he
      simp only [neg_div] at he ⊢
      linarith [he]
    simp only [approximation, ite_eq_right hs, Rat.cast_div, Rat.cast_neg, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat]
    rw [he', abs_of_nonneg (div_nonneg hr.1 hd.le)]
    exact div_le_div_of_nonneg_right hr.2 hd.le

end Maxwell.Cost.RealRound
