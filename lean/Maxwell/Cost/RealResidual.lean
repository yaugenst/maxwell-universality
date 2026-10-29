import Maxwell.Cost.RealSparse
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A finite Real-RAM residual verifier. The product vector is read from
machine memory, as produced by `RealSparse`; the right-hand side, tolerance,
and dimension are read by charged instructions from typed input. -/

namespace Maxwell.Cost.RealResidual

open RealSparse (execute execute_sound execute_add)

set_option maxRecDepth 20000

noncomputable def input (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) : RAMInput where
  words a := if a < n then rhs a else tolerance
  indices a := if a = 0 then n else 0

@[simp] theorem input_count (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) :
    (input n rhs tolerance).indices 0 = n := by simp [input]

theorem input_rhs (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) (j : ℕ) (hj : j < n) :
    (input n rhs tolerance).words j = rhs j := by simp [input, hj]

@[simp] theorem input_tolerance (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) :
    (input n rhs tolerance).words n = tolerance := by simp [input]

/-- Both comparison branches take the same number of actual transitions. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .inputIndex 2 0,
  .indexLiteral 3 0, .indexLiteral 4 16,
  .literal 0 0, .literal 1 0, .literal 2 (-1),
  .branchIndexLE 2 3 20 9,
  .indexAdd 5 4 3, .load 3 5, .input 4 3,
  .multiply 5 2 4, .add 3 3 5, .multiply 3 3 3,
  .add 0 0 3, .multiply 4 4 4, .add 1 1 4,
  .indexAdd 3 3 1, .jump 8,
  .input 6 2, .multiply 6 6 6, .multiply 6 6 1,
  .branchLE 0 6 24 27,
  .literal 7 1, .output 7, .jump 30,
  .literal 7 0, .output 7, .jump 30, .halt]⟩

def Ready (s : RAMState) (n k : ℕ) : Prop :=
  s.pc = 8 ∧ s.indices 1 = 1 ∧ s.indices 2 = n ∧
    s.indices 3 = k ∧ s.indices 4 = 16 ∧ s.words 2 = -1

noncomputable def initialized (s : RAMState) (n : ℕ) : RAMState :=
  let s := {s with pc := 0}
  let s := s.setIndex 0 0
  let s := s.setIndex 1 1
  let s := s.setIndex 2 n
  let s := s.setIndex 3 0
  let s := s.setIndex 4 16
  let s := s.setWord 0 0
  let s := s.setWord 1 0
  s.setWord 2 (-1)

theorem initialize_steps (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ)
    (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 0) :
    execute (program.next (input n rhs tolerance) tape) 8 s = some (initialized s n) := by
  simp [execute, program, Machine.next, initialized, RAMState.setIndex, RAMState.setWord, hpc]

theorem initialized_ready (s : RAMState) (n : ℕ) : Ready (initialized s n) n 0 := by
  simp [Ready, initialized, RAMState.setIndex, RAMState.setWord]

theorem initialized_memory (s : RAMState) (n j : ℕ) :
    (initialized s n).words (16 + j) = s.words (16 + j) := by
  have h : 16 + j ≠ 0 ∧ 16 + j ≠ 1 ∧ 16 + j ≠ 2 := by omega
  simp [initialized, RAMState.setIndex, RAMState.setWord, h]

noncomputable def advanced (s : RAMState) (x b : ℝ) : RAMState :=
  let t := {s with pc := 9}
  let t := t.setIndex 5 (16 + s.indices 3)
  let t := t.setWord 3 x
  let t := t.setWord 4 b
  let t := t.setWord 5 (-b)
  let t := t.setWord 3 (x - b)
  let t := t.setWord 3 ((x - b) ^ 2)
  let t := t.setWord 0 (s.words 0 + (x - b) ^ 2)
  let t := t.setWord 4 (b ^ 2)
  let t := t.setWord 1 (s.words 1 + b ^ 2)
  let t := t.setIndex 3 (s.indices 3 + 1)
  {t with pc := 8}

noncomputable def middle (s : RAMState) (x b : ℝ) : RAMState :=
  let t := {s with pc := 9}
  let t := t.setIndex 5 (16 + s.indices 3)
  let t := t.setWord 3 x
  let t := t.setWord 4 b
  let t := t.setWord 5 (-b)
  t.setWord 3 (x - b)

set_option maxHeartbeats 1000000 in
theorem cycle (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) (tape : ℕ → Bool)
    (s : RAMState) (k : ℕ) (hready : Ready s n k) (hk : k < n) :
    execute (program.next (input n rhs tolerance) tape) 12 s =
      some (advanced s (s.words (16 + k)) (rhs k)) := by
  rcases hready with ⟨hpc, h1, hn, hk', hb, hm⟩
  have hnot : ¬ n ≤ k := by omega
  have hfirst : execute (program.next (input n rhs tolerance) tape) 6 s =
      some (middle s (s.words (16 + k)) (rhs k)) := by
    simp [execute, program, Machine.next, hpc, hn, hk', hb, hm, hnot,
      RAMState.setIndex, RAMState.setWord, input_rhs, hk, middle, sub_eq_add_neg]
  rw [show 12 = 6 + 6 from rfl, execute_add, hfirst, Option.bind_some]
  simp [execute, program, Machine.next, h1, hk', RAMState.setIndex,
    RAMState.setWord, middle, advanced, pow_two]

theorem advanced_ready (s : RAMState) (n k : ℕ) (h : Ready s n k) (x b : ℝ) :
    Ready (advanced s x b) n (k + 1) := by
  rcases h with ⟨_, h1, hn, hk, hb, hm⟩
  simp [Ready, advanced, RAMState.setIndex, RAMState.setWord, h1, hn, hk, hb, hm]

theorem advanced_memory (s : RAMState) (x b : ℝ) (j : ℕ) :
    (advanced s x b).words (16 + j) = s.words (16 + j) := by
  have h : 16 + j ≠ 0 ∧ 16 + j ≠ 1 ∧ 16 + j ≠ 3 ∧ 16 + j ≠ 4 ∧ 16 + j ≠ 5 := by omega
  simp [advanced, RAMState.setIndex, RAMState.setWord, h]

@[simp] theorem advanced_sum (s : RAMState) (x b : ℝ) :
    (advanced s x b).words 0 = s.words 0 + (x - b) ^ 2 := by
  simp [advanced, RAMState.setIndex, RAMState.setWord]

@[simp] theorem advanced_rhs_sum (s : RAMState) (x b : ℝ) :
    (advanced s x b).words 1 = s.words 1 + b ^ 2 := by
  simp [advanced, RAMState.setIndex, RAMState.setWord]

noncomputable def decision (residualSq rhsSq tolerance : ℝ) : ℝ :=
  if residualSq ≤ tolerance ^ 2 * rhsSq then 1 else 0

noncomputable def finished (s : RAMState) (tolerance : ℝ) : RAMState :=
  let t := {s with pc := 20}
  let t := t.setWord 6 tolerance
  let t := t.setWord 6 (tolerance ^ 2)
  let t := t.setWord 6 (tolerance ^ 2 * s.words 1)
  let t := t.setWord 7 (decision (s.words 0) (s.words 1) tolerance)
  {t with pc := 30, output := decision (s.words 0) (s.words 1) tolerance :: s.output}

set_option maxHeartbeats 1000000 in
theorem finish_steps (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) (tape : ℕ → Bool)
    (s : RAMState) (hready : Ready s n n) :
    execute (program.next (input n rhs tolerance) tape) 8 s = some (finished s tolerance) := by
  rcases hready with ⟨hpc, _, hn, hk, _, _⟩
  by_cases htest : s.words 0 ≤ tolerance * tolerance * s.words 1
  · simp [execute, program, Machine.next, hpc, hn, hk, RAMState.setIndex,
      RAMState.setWord, finished, decision, pow_two, htest]
  · simp [execute, program, Machine.next, hpc, hn, hk, RAMState.setIndex,
      RAMState.setWord, finished, decision, pow_two, htest]

theorem finished_halt (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) (tape : ℕ → Bool) (s : RAMState) :
    program.next (input n rhs tolerance) tape (finished s tolerance) = none := by
  simp [program, Machine.next, finished]

@[simp] theorem finished_sum (s : RAMState) (tolerance : ℝ) :
    (finished s tolerance).words 0 = s.words 0 := by simp [finished, RAMState.setWord]

@[simp] theorem finished_rhs_sum (s : RAMState) (tolerance : ℝ) :
    (finished s tolerance).words 1 = s.words 1 := by simp [finished, RAMState.setWord]

theorem finished_memory (s : RAMState) (tolerance : ℝ) (j : ℕ) :
    (finished s tolerance).words (16 + j) = s.words (16 + j) := by
  have h : 16 + j ≠ 6 ∧ 16 + j ≠ 7 := by omega
  simp [finished, RAMState.setWord, h]

/-- Accumulates the actual residual squares without modifying product memory. -/
theorem scan (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) (tape : ℕ → Bool)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (hready : Ready s n k) (hcount : k + remaining = n) :
    ∃ final : RAMState,
      Steps (program.next (input n rhs tolerance) tape) (12 * remaining) s final ∧
      Ready final n n ∧
      final.words 0 = s.words 0 + ∑ i ∈ Finset.range remaining, (s.words (16 + (k + i)) - rhs (k + i)) ^ 2 ∧
      final.words 1 = s.words 1 + ∑ i ∈ Finset.range remaining, rhs (k + i) ^ 2 ∧
      (∀ j, final.words (16 + j) = s.words (16 + j)) ∧
      final.randomCursor = s.randomCursor ∧ final.output = s.output := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, hready, by simp, by simp, fun _ => rfl, rfl, rfl⟩
  | succ remaining ih =>
    have hk : k < n := by omega
    let next := advanced s (s.words (16 + k)) (rhs k)
    have hsteps := execute_sound _ (cycle n rhs tolerance tape s k hready hk)
    obtain ⟨final, hrun, hready', hsum, hrhssum, hmem, hrandom, hout⟩ := ih next (k + 1)
      (advanced_ready s n k hready _ _) (by omega)
    refine ⟨final, ?_, hready', ?_, ?_, ?_, hrandom, hout⟩
    · convert hsteps.trans hrun using 1
      omega
    · rw [hsum, advanced_sum]
      simp only [next, advanced_memory]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero]
      have hi : ∀ i : ℕ, k + 1 + i = k + (i + 1) := by omega
      simp only [hi]
      ring
    · rw [hrhssum, advanced_rhs_sum, Finset.sum_range_succ']
      simp only [Nat.add_zero]
      have hi : ∀ i : ℕ, k + 1 + i = k + (i + 1) := by omega
      simp only [hi]
      ring
    · intro j
      exact (hmem j).trans (advanced_memory s _ _ j)

noncomputable def residualSq (n : ℕ) (s : RAMState) (rhs : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (s.words (16 + j) - rhs j) ^ 2

noncomputable def rhsSq (n : ℕ) (rhs : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, rhs j ^ 2

/-- The component starts at its first instruction and consumes the existing
product memory. Its runtime includes all input reads and the final decision. -/
theorem terminates (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc = 0) :
    ∃ final : RAMState,
      Terminates (program.next (input n rhs tolerance) tape) (12 * n + 16) s final ∧
      final.words 0 = residualSq n s rhs ∧ final.words 1 = rhsSq n rhs ∧
      final.output = decision (residualSq n s rhs) (rhsSq n rhs) tolerance :: s.output ∧
      (∀ j, final.words (16 + j) = s.words (16 + j)) ∧ final.randomCursor = s.randomCursor := by
  have hinit := execute_sound _ (initialize_steps n rhs tolerance tape s hpc)
  obtain ⟨t, hscan, hready, hsum, hrhs, hmem, hrandom, hout⟩ :=
    scan n rhs tolerance tape n (initialized s n) 0 (initialized_ready s n) (by omega)
  have hs : t.words 0 = residualSq n s rhs := by
    simp only [initialized_memory] at hsum
    simpa [residualSq, initialized, RAMState.setIndex, RAMState.setWord] using hsum
  have hb : t.words 1 = rhsSq n rhs := by
    simpa [rhsSq, initialized, RAMState.setIndex, RAMState.setWord] using hrhs
  have hfinish := execute_sound _ (finish_steps n rhs tolerance tape t hready)
  refine ⟨finished t tolerance, ?_, ?_, ?_, ?_, ?_, hrandom⟩
  · convert ((hinit.trans hscan).trans hfinish).terminates
      (Terminates.halt _ (finished_halt n rhs tolerance tape t)) using 1
    omega
  · simpa using hs
  · simpa using hb
  · change decision (t.words 0) (t.words 1) tolerance :: t.output = _
    rw [hs, hb, hout]
    rfl
  · intro j
    exact (finished_memory t tolerance j).trans ((hmem j).trans (initialized_memory s n j))

/-- A capped invocation cannot return a fabricated verdict on timeout. -/
theorem run (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc = 0) :
    ∃ final : RAMState,
      (runCapped (program.next (input n rhs tolerance) tape) (12 * n + 17) s).finished = some final ∧
      (runCapped (program.next (input n rhs tolerance) tape) (12 * n + 17) s).instructions = 12 * n + 16 ∧
      final.output = decision (residualSq n s rhs) (rhsSq n rhs) tolerance :: s.output := by
  obtain ⟨final, ht, _, _, hout, _, _⟩ := terminates n rhs tolerance tape s hpc
  obtain ⟨hf, hc⟩ := runCapped_of_terminates _ ht
  exact ⟨final, hf, hc, hout⟩

/-- The finite Euclidean vector actually stored in the product memory. -/
noncomputable def memoryVector (n : ℕ) (s : RAMState) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => s.words (16 + j.val))

noncomputable def rhsVector (n : ℕ) (rhs : ℕ → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => rhs j.val)

theorem residualSq_eq_norm_sq (n : ℕ) (s : RAMState) (rhs : ℕ → ℝ) :
    residualSq n s rhs = ‖memoryVector n s - rhsVector n rhs‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ j ∈ Finset.range n, (s.words (16 + j) - rhs j) ^ 2) =
    ∑ j : Fin n, (s.words (16 + j.val) - rhs j.val) ^ 2
  exact (Fin.sum_univ_eq_sum_range _ n).symm

theorem rhsSq_eq_norm_sq (n : ℕ) (rhs : ℕ → ℝ) :
    rhsSq n rhs = ‖rhsVector n rhs‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (Fin.sum_univ_eq_sum_range (fun j => rhs j ^ 2) n).symm

/-- The machine's comparison is precisely relative Euclidean residual
verification, including a zero right-hand side. -/
theorem decision_eq_one_iff (n : ℕ) (s : RAMState) (rhs : ℕ → ℝ)
    (tolerance : ℝ) (ht : 0 ≤ tolerance) :
    decision (residualSq n s rhs) (rhsSq n rhs) tolerance = 1 ↔
      ‖memoryVector n s - rhsVector n rhs‖ ≤ tolerance * ‖rhsVector n rhs‖ := by
  rw [decision, residualSq_eq_norm_sq, rhsSq_eq_norm_sq]
  have hs : ‖memoryVector n s - rhsVector n rhs‖ ^ 2 ≤ tolerance ^ 2 * ‖rhsVector n rhs‖ ^ 2 ↔
      ‖memoryVector n s - rhsVector n rhs‖ ≤ tolerance * ‖rhsVector n rhs‖ := by
    rw [← mul_pow]
    exact sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))
  split_ifs with h
  · exact iff_of_true rfl (hs.mp h)
  · exact iff_of_false (by norm_num) (fun hh => h (hs.mpr hh))

/-- Acceptance and rejection both have the same exact linear runtime. -/
theorem verifies (n : ℕ) (rhs : ℕ → ℝ) (tolerance : ℝ) (ht : 0 ≤ tolerance)
    (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 0) :
    ∃ final : RAMState,
      (runCapped (program.next (input n rhs tolerance) tape) (12 * n + 17) s).finished = some final ∧
      (runCapped (program.next (input n rhs tolerance) tape) (12 * n + 17) s).instructions = 12 * n + 16 ∧
      (final.output = 1 :: s.output ↔
        ‖memoryVector n s - rhsVector n rhs‖ ≤ tolerance * ‖rhsVector n rhs‖) := by
  obtain ⟨final, hf, hc, ho⟩ := run n rhs tolerance tape s hpc
  refine ⟨final, hf, hc, ?_⟩
  rw [ho, List.cons.injEq]
  simpa using decision_eq_one_iff n s rhs tolerance ht

end Maxwell.Cost.RealResidual
