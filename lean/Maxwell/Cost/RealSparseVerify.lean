import Maxwell.Cost.RealResidual

/-! One finite program computes a sparse product and verifies its residual.
All data enter through the typed input tapes; the machine starts with empty
memory. Sparse records are never replaced by a host-computed product. -/

namespace Maxwell.Cost.RealSparseVerify

open RealSparse (execute execute_sound entryAt)

set_option maxRecDepth 20000

theorem execute_add {σ : Type} (next : σ → Option σ) (a b : ℕ) (s : σ) :
    execute next (a + b) s = (execute next a s).bind (execute next b) := by
  induction a generalizing s with
  | zero => simp [execute]
  | succ a ih =>
    rw [Nat.succ_add, execute]
    cases h : next s with
    | none => simp [execute, h]
    | some t => simp [execute, h, ih]

/-- The two real vector blocks are the candidate and right-hand side. -/
noncomputable def input (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (tolerance : ℝ) : RAMInput where
  words a := if a < entries.length then (entryAt entries a).value else
    if a < entries.length + n then x (a - entries.length) else
    if a < entries.length + n + n then rhs (a - (entries.length + n)) else tolerance
  indices a := if a = 0 then entries.length else
    if a = 1 + 2 * entries.length then n else
    if (a - 1) % 2 = 0 then (entryAt entries ((a - 1) / 2)).row
    else (entryAt entries ((a - 1) / 2)).column

@[simp] theorem input_count (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) (t : ℝ) :
    (input entries n x rhs t).indices 0 = entries.length := by simp [input]

theorem input_row (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) (t : ℝ)
    (k : ℕ) (hk : k < entries.length) :
    (input entries n x rhs t).indices (1 + 2 * k) = (entryAt entries k).row := by
  simp [input, hk.ne, Nat.mul_comm]

theorem input_column (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    (input entries n x rhs t).indices (2 + 2 * k) = (entryAt entries k).column := by
  have hne : 2 + 2 * k ≠ 1 + 2 * entries.length := by omega
  have hsub : 2 + 2 * k - 1 = 2 * k + 1 := by omega
  simp [input, hne, hsub, Nat.add_div, Nat.add_mod]

theorem input_value (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) (t : ℝ)
    (k : ℕ) (hk : k < entries.length) :
    (input entries n x rhs t).words k = (entryAt entries k).value := by simp [input, hk]

theorem input_candidate (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) (t : ℝ)
    (j : ℕ) (hj : j < n) :
    (input entries n x rhs t).words (entries.length + j) = x j := by
  simp [input, hj]

@[simp] theorem input_dimension (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) (t : ℝ) :
    (input entries n x rhs t).indices (1 + 2 * entries.length) = n := by simp [input]

theorem input_rhs (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) (t : ℝ)
    (j : ℕ) (hj : j < n) :
    (input entries n x rhs t).words (entries.length + n + j) = rhs j := by
  have h1 : ¬ entries.length + n + j < entries.length := by omega
  have h2 : ¬ entries.length + n + j < entries.length + n := by omega
  have h3 : entries.length + n + j < entries.length + n + n := by omega
  simp [input, h1, h2, h3]

@[simp] theorem input_tolerance (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) (t : ℝ) :
    (input entries n x rhs t).words (entries.length + n + n) = t := by
  have h : ¬ entries.length + n + n < entries.length := by omega
  simp [input, h]

/-- The sparse loop is followed directly by the residual loop. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .inputIndex 2 0,
  .indexLiteral 3 0, .indexLiteral 4 1, .indexLiteral 10 16,
  .branchIndexLE 2 3 21 7,
  .inputIndex 5 4, .indexAdd 4 4 1, .inputIndex 6 4,
  .input 0 3, .indexAdd 7 2 5, .input 1 7,
  .indexAdd 8 10 6, .load 2 8, .multiply 3 0 1,
  .add 2 2 3, .store 8 2,
  .indexAdd 3 3 1, .indexAdd 4 4 1, .jump 6,
  .indexCopy 0 4, .inputIndex 11 0, .indexAdd 12 2 11,
  .indexLiteral 0 0, .indexLiteral 1 1, .indexCopy 2 11,
  .indexLiteral 3 0, .indexLiteral 4 16,
  .literal 0 0, .literal 1 0, .literal 2 (-1),
  .branchIndexLE 2 3 45 33,
  .indexAdd 5 4 3, .load 3 5, .indexAdd 6 12 3, .input 4 6,
  .multiply 5 2 4, .add 3 3 5, .multiply 3 3 3,
  .add 0 0 3, .multiply 4 4 4, .add 1 1 4,
  .indexAdd 3 3 1, .jump 32,
  .indexAdd 6 12 2, .input 6 6, .multiply 6 6 6, .multiply 6 6 1,
  .branchLE 0 6 50 53,
  .literal 7 1, .output 7, .jump 56,
  .literal 7 0, .output 7, .jump 56, .halt]⟩

theorem sparse_initialize (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) :
    execute (program.next (input entries n x rhs t) tape) 6 RAMState.initial =
      some (RealSparse.initialized entries.length) := by
  simp [execute, program, Machine.next, RAMState.initial, RAMState.setIndex, RealSparse.initialized]

noncomputable def sparseMiddle (s : RAMState) (e : SparseEntry) (x : ℝ) : RAMState :=
  let t := {s with pc := 7}
  let t := t.setIndex 5 e.row
  let t := t.setIndex 4 (s.indices 4 + 1)
  let t := t.setIndex 6 e.column
  let t := t.setWord 0 e.value
  let t := t.setIndex 7 (s.indices 2 + e.row)
  t.setWord 1 x

set_option maxHeartbeats 1400000 in
theorem sparse_cycle (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (s : RAMState) (k : ℕ)
    (hready : RealSparse.Ready s entries.length k) (hk : k < entries.length)
    (hrow : (entryAt entries k).row < n) :
    execute (program.next (input entries n x rhs t) tape) 15 s =
      some (RealSparse.advanced s (entryAt entries k) (x (entryAt entries k).row)) := by
  rcases hready with ⟨hpc, _, h1, hm, hi, ha, hb⟩
  have hnot : ¬ entries.length ≤ k := by omega
  have haddr : 1 + 2 * k + 1 = 2 + 2 * k := by omega
  have hlarge : ∀ j : ℕ, 16 + j ≠ 0 ∧ 16 + j ≠ 1 ∧ 16 + j ≠ 2 ∧ 16 + j ≠ 3 := by omega
  have hfirst : execute (program.next (input entries n x rhs t) tape) 7 s =
      some (sparseMiddle s (entryAt entries k) (x (entryAt entries k).row)) := by
    simp (config := { maxSteps := 100000 }) [execute, program, Machine.next,
      hpc, h1, hm, hi, ha, hnot, RAMState.setWord, RAMState.setIndex,
      input_row, input_column, input_value, input_candidate, hk, hrow, haddr, sparseMiddle]
  rw [show 15 = 7 + 8 from rfl, execute_add, hfirst, Option.bind_some]
  simp (config := { maxSteps := 100000 }) [execute, program, Machine.next,
    h1, hm, hi, ha, hb, RAMState.setWord, RAMState.setIndex,
    hlarge, sparseMiddle, RealSparse.advanced, Nat.add_assoc]

/-- Sparse accumulation is an actual segment of the combined machine. -/
theorem sparse_scan (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (hrows : ∀ k < entries.length, (entryAt entries k).row < n)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (hready : RealSparse.Ready s entries.length k)
    (hcount : k + remaining = entries.length) :
    ∃ final : RAMState,
      Steps (program.next (input entries n x rhs t) tape) (15 * remaining) s final ∧
      RealSparse.Ready final entries.length entries.length ∧
      (∀ j, final.words (16 + j) = s.words (16 + j) +
        ∑ i ∈ Finset.range remaining, RealSparse.contribution entries x (k + i) j) ∧
      final.randomCursor = s.randomCursor ∧ final.output = s.output := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k = entries.length := by omega
    subst k
    exact ⟨s, Steps.refl s, hready, by intro j; simp, rfl, rfl⟩
  | succ remaining ih =>
    have hk : k < entries.length := by omega
    let next := RealSparse.advanced s (entryAt entries k) (x (entryAt entries k).row)
    have hsteps := execute_sound _ (sparse_cycle entries n x rhs t tape s k hready hk (hrows k hk))
    obtain ⟨final, hrun, hready', hmemory, hrandom, hout⟩ := ih next (k + 1)
      (RealSparse.advanced_ready s _ k hready _ _) (by omega)
    refine ⟨final, ?_, hready', ?_, hrandom, hout⟩
    · convert hsteps.trans hrun using 1
      omega
    · intro j
      rw [hmemory, RealSparse.advanced_memory, Finset.sum_range_succ']
      simp only [Nat.add_zero, RealSparse.contribution]
      have hi : ∀ i : ℕ, k + 1 + i = k + (i + 1) := by omega
      simp only [hi]
      ring

def Ready (s : RAMState) (m n k : ℕ) : Prop :=
  s.pc = 32 ∧ s.indices 1 = 1 ∧ s.indices 2 = n ∧ s.indices 3 = k ∧
    s.indices 4 = 16 ∧ s.indices 12 = m + n ∧ s.words 2 = -1

noncomputable def initialized (s : RAMState) (m n : ℕ) : RAMState :=
  let t := {s with pc := 21}
  let t := t.setIndex 0 (1 + 2 * m)
  let t := t.setIndex 11 n
  let t := t.setIndex 12 (m + n)
  let t := t.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 2 n
  let t := t.setIndex 3 0
  let t := t.setIndex 4 16
  let t := t.setWord 0 0
  let t := t.setWord 1 0
  t.setWord 2 (-1)

theorem initialize_steps (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (s : RAMState)
    (hready : RealSparse.Ready s entries.length entries.length) :
    execute (program.next (input entries n x rhs t) tape) 12 s = some (initialized s entries.length n) := by
  rcases hready with ⟨hpc, _, _, hm, hk, ha, _⟩
  simp [execute, program, Machine.next, hpc, hm, hk, ha, initialized, RAMState.setIndex, RAMState.setWord]

theorem initialized_ready (s : RAMState) (m n : ℕ) : Ready (initialized s m n) m n 0 := by
  simp [Ready, initialized, RAMState.setIndex, RAMState.setWord]

theorem initialized_memory (s : RAMState) (m n j : ℕ) :
    (initialized s m n).words (16 + j) = s.words (16 + j) := by
  have h : 16 + j ≠ 0 ∧ 16 + j ≠ 1 ∧ 16 + j ≠ 2 := by omega
  simp [initialized, RAMState.setIndex, RAMState.setWord, h]

noncomputable def advanced (s : RAMState) (x b : ℝ) : RAMState :=
  let t := RealResidual.advanced s x b
  {t with pc := 32, indices := Function.update t.indices 6 (s.indices 12 + s.indices 3)}

noncomputable def middle (s : RAMState) (x b : ℝ) : RAMState :=
  let t := {s with pc := 33}
  let t := t.setIndex 5 (16 + s.indices 3)
  let t := t.setWord 3 x
  let t := t.setIndex 6 (s.indices 12 + s.indices 3)
  let t := t.setWord 4 b
  let t := t.setWord 5 (-b)
  t.setWord 3 (x - b)

set_option maxHeartbeats 1400000 in
theorem cycle (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (s : RAMState) (k : ℕ)
    (hready : Ready s entries.length n k) (hk : k < n) :
    execute (program.next (input entries n x rhs t) tape) 13 s =
      some (advanced s (s.words (16 + k)) (rhs k)) := by
  rcases hready with ⟨hpc, h1, hn, hk', hb, hbase, hm⟩
  have hnot : ¬ n ≤ k := by omega
  have hfirst : execute (program.next (input entries n x rhs t) tape) 7 s =
      some (middle s (s.words (16 + k)) (rhs k)) := by
    simp (config := { maxSteps := 100000 }) [execute, program, Machine.next,
      hpc, hn, hk', hb, hbase, hm, hnot, RAMState.setIndex, RAMState.setWord,
      input_rhs, hk, middle, sub_eq_add_neg]
  rw [show 13 = 7 + 6 from rfl, execute_add, hfirst, Option.bind_some]
  simp (config := { maxSteps := 100000 }) [execute, program, Machine.next,
    h1, hk', hbase, RAMState.setIndex, RAMState.setWord, middle, advanced, RealResidual.advanced,
    pow_two, Function.update_comm (show (3 : ℕ) ≠ 6 by omega)]

theorem advanced_ready (s : RAMState) (m n k : ℕ) (h : Ready s m n k) (x b : ℝ) :
    Ready (advanced s x b) m n (k + 1) := by
  rcases h with ⟨_, h1, hn, hk, hb, hbase, hm⟩
  simp [Ready, advanced, RealResidual.advanced, RAMState.setIndex, RAMState.setWord,
    h1, hn, hk, hb, hbase, hm]

@[simp] theorem advanced_memory (s : RAMState) (x b : ℝ) (j : ℕ) :
    (advanced s x b).words (16 + j) = s.words (16 + j) :=
  RealResidual.advanced_memory s x b j

@[simp] theorem advanced_sum (s : RAMState) (x b : ℝ) :
    (advanced s x b).words 0 = s.words 0 + (x - b) ^ 2 :=
  RealResidual.advanced_sum s x b

@[simp] theorem advanced_rhs_sum (s : RAMState) (x b : ℝ) :
    (advanced s x b).words 1 = s.words 1 + b ^ 2 :=
  RealResidual.advanced_rhs_sum s x b

theorem scan (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (remaining : ℕ) (s : RAMState) (k : ℕ)
    (hready : Ready s entries.length n k) (hcount : k + remaining = n) :
    ∃ final : RAMState,
      Steps (program.next (input entries n x rhs t) tape) (13 * remaining) s final ∧
      Ready final entries.length n n ∧
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
    have hsteps := execute_sound _ (cycle entries n x rhs t tape s k hready hk)
    obtain ⟨final, hrun, hready', hsum, hrhssum, hmem, hrandom, hout⟩ := ih next (k + 1)
      (advanced_ready s entries.length n k hready _ _) (by omega)
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

noncomputable def finished (s : RAMState) (t : ℝ) : RAMState :=
  let f := RealResidual.finished s t
  {f with pc := 56, indices := Function.update f.indices 6 (s.indices 12 + s.indices 2)}

set_option maxHeartbeats 1400000 in
theorem finish_steps (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (s : RAMState) (hready : Ready s entries.length n n) :
    execute (program.next (input entries n x rhs t) tape) 9 s = some (finished s t) := by
  rcases hready with ⟨hpc, _, hn, hk, _, hbase, _⟩
  let middle := (({s with pc := 45}).setIndex 6 (entries.length + n + n)).setWord 6 t
  have hf : execute (program.next (input entries n x rhs t) tape) 3 s = some middle := by
    simp [execute, program, Machine.next, hpc, hn, hk, hbase,
      middle, RAMState.setIndex, RAMState.setWord]
  rw [show 9 = 3 + 6 from rfl, execute_add, hf, Option.bind_some]
  by_cases htest : s.words 0 ≤ t * t * s.words 1
  · simp (config := { maxSteps := 100000 }) [execute, program, Machine.next, middle, hn, hbase,
      RAMState.setIndex, RAMState.setWord, finished, RealResidual.finished, RealResidual.decision,
      pow_two, htest]
  · simp (config := { maxSteps := 100000 }) [execute, program, Machine.next, middle, hn, hbase,
      RAMState.setIndex, RAMState.setWord, finished, RealResidual.finished, RealResidual.decision,
      pow_two, htest]

theorem finished_halt (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (s : RAMState) :
    program.next (input entries n x rhs t) tape (finished s t) = none := by
  simp [program, Machine.next, finished]

noncomputable def residualSq (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (RealSparse.transposeSum entries x j - rhs j) ^ 2

/-- The initial state contains no product or residual advice. Both are
computed by this single finite machine before it emits its verdict. -/
theorem terminates (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (hrows : ∀ k < entries.length, (entryAt entries k).row < n) :
    ∃ final : RAMState,
      Terminates (program.next (input entries n x rhs t) tape) (15 * entries.length + 13 * n + 27)
        RAMState.initial final ∧
      final.output = [RealResidual.decision (residualSq entries n x rhs) (RealResidual.rhsSq n rhs) t] ∧
      (∀ j, final.words (16 + j) = RealSparse.transposeSum entries x j) ∧
      final.randomCursor = 0 := by
  have hstart := execute_sound _ (sparse_initialize entries n x rhs t tape)
  obtain ⟨p, hp, hpr, hpm, hprand, hpout⟩ := sparse_scan entries n x rhs t tape hrows
    entries.length (RealSparse.initialized entries.length) 0 (RealSparse.initialized_ready _) (by omega)
  have hproduct : ∀ j, p.words (16 + j) = RealSparse.transposeSum entries x j := by
    intro j
    simpa [RealSparse.initialized, RAMState.setIndex, RAMState.initial, RealSparse.transposeSum] using hpm j
  have hi := execute_sound _ (initialize_steps entries n x rhs t tape p hpr)
  obtain ⟨r, hr, hrr, hrs, hrb, hrm, hrrand, hrout⟩ := scan entries n x rhs t tape
    n (initialized p entries.length n) 0 (initialized_ready p entries.length n) (by omega)
  have hs : r.words 0 = residualSq entries n x rhs := by
    simp only [initialized_memory, hproduct] at hrs
    simpa [residualSq, initialized, RAMState.setIndex, RAMState.setWord] using hrs
  have hb : r.words 1 = RealResidual.rhsSq n rhs := by
    simpa [RealResidual.rhsSq, initialized, RAMState.setIndex, RAMState.setWord] using hrb
  have hf := execute_sound _ (finish_steps entries n x rhs t tape r hrr)
  refine ⟨finished r t, ?_, ?_, ?_, hrrand.trans hprand⟩
  · convert ((((hstart.trans hp).trans hi).trans hr).trans hf).terminates
      (Terminates.halt _ (finished_halt entries n x rhs t tape r)) using 1
    omega
  · change RealResidual.decision (r.words 0) (r.words 1) t :: r.output = _
    rw [hs, hb, hrout]
    change _ :: p.output = _
    rw [hpout]
    rfl
  · intro j
    exact (RealResidual.finished_memory r t j).trans
      ((hrm j).trans ((initialized_memory p entries.length n j).trans (hproduct j)))

/-- Operational cap for the same program, valid on every width and
regardless of whether its residual comparison accepts. -/
theorem run (entries : List SparseEntry) (n : ℕ) (x rhs : ℕ → ℝ)
    (t : ℝ) (tape : ℕ → Bool) (hrows : ∀ k < entries.length, (entryAt entries k).row < n) :
    ∃ final : RAMState,
      (program.run (input entries n x rhs t) tape (15 * entries.length + 13 * n + 28)).finished = some final ∧
      (program.run (input entries n x rhs t) tape (15 * entries.length + 13 * n + 28)).instructions =
        15 * entries.length + 13 * n + 27 ∧
      final.output = [RealResidual.decision (residualSq entries n x rhs) (RealResidual.rhsSq n rhs) t] := by
  obtain ⟨final, ht, ho, _, _⟩ := terminates entries n x rhs t tape hrows
  obtain ⟨hf, hc⟩ := runCapped_of_terminates _ ht
  exact ⟨final, hf, hc, ho⟩

theorem residualSq_eq_norm_sq (entries : List SparseEntry) (n : ℕ)
    (hrows : ∀ k < entries.length, (entryAt entries k).row < n)
    (x rhs : EuclideanSpace ℝ (Fin n)) :
    residualSq entries n (RealSparse.vectorInput x) (RealSparse.vectorInput rhs) =
      ‖WithLp.toLp 2 ((RealSparse.rectangularMatrix n n entries).transpose.mulVec x) - rhs‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold residualSq
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [RealSparse.transposeSum_eq_mulVec n n entries hrows x j]
  simp [RealSparse.vectorInput, j.isLt]

theorem rhsSq_eq_norm_sq (n : ℕ) (rhs : EuclideanSpace ℝ (Fin n)) :
    RealResidual.rhsSq n (RealSparse.vectorInput rhs) = ‖rhs‖ ^ 2 := by
  rw [RealResidual.rhsSq_eq_norm_sq]
  congr 2
  ext j
  simp [RealResidual.rhsVector, RealSparse.vectorInput]

/-- The verdict concerns the actual sparse matrix and actual candidate.
No mathematical product is supplied in the initial machine state. -/
theorem verifies (entries : List SparseEntry) (n : ℕ)
    (hrows : ∀ k < entries.length, (entryAt entries k).row < n)
    (x rhs : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 ≤ t) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      (program.run (input entries n (RealSparse.vectorInput x) (RealSparse.vectorInput rhs) t)
        tape (15 * entries.length + 13 * n + 28)).finished = some final ∧
      (program.run (input entries n (RealSparse.vectorInput x) (RealSparse.vectorInput rhs) t)
        tape (15 * entries.length + 13 * n + 28)).instructions = 15 * entries.length + 13 * n + 27 ∧
      (final.output = [1] ↔
        ‖WithLp.toLp 2 ((RealSparse.rectangularMatrix n n entries).transpose.mulVec x) - rhs‖ ≤ t * ‖rhs‖) := by
  obtain ⟨final, hf, hc, ho⟩ := run entries n (RealSparse.vectorInput x) (RealSparse.vectorInput rhs) t tape hrows
  refine ⟨final, hf, hc, ?_⟩
  rw [ho, List.cons.injEq]
  simp only [and_true]
  rw [RealResidual.decision, residualSq_eq_norm_sq entries n hrows x rhs, rhsSq_eq_norm_sq]
  have hs : ‖WithLp.toLp 2 ((RealSparse.rectangularMatrix n n entries).transpose.mulVec x) - rhs‖ ^ 2 ≤ t ^ 2 * ‖rhs‖ ^ 2 ↔
      ‖WithLp.toLp 2 ((RealSparse.rectangularMatrix n n entries).transpose.mulVec x) - rhs‖ ≤ t * ‖rhs‖ := by
    rw [← mul_pow]
    exact sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))
  split_ifs with h
  · exact iff_of_true rfl (hs.mp h)
  · exact iff_of_false (by norm_num) (fun hh => h (hs.mpr hh))

/-- In particular the same machine verifies a symmetric saddle matrix;
its transpose is the original matrix, with no extra arithmetic pass. -/
theorem symmetric_verifies (entries : List SparseEntry) (n : ℕ)
    (hrows : ∀ k < entries.length, (entryAt entries k).row < n)
    (hsym : (RealSparse.rectangularMatrix n n entries).IsSymm)
    (x rhs : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 ≤ t) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      (program.run (input entries n (RealSparse.vectorInput x) (RealSparse.vectorInput rhs) t)
        tape (15 * entries.length + 13 * n + 28)).finished = some final ∧
      (program.run (input entries n (RealSparse.vectorInput x) (RealSparse.vectorInput rhs) t)
        tape (15 * entries.length + 13 * n + 28)).instructions = 15 * entries.length + 13 * n + 27 ∧
      (final.output = [1] ↔
        ‖WithLp.toLp 2 ((RealSparse.rectangularMatrix n n entries).mulVec x) - rhs‖ ≤ t * ‖rhs‖) := by
  simpa only [hsym.eq] using verifies entries n hrows x rhs t ht tape

/-- When active dimension is bounded by the sparse record count, the
concrete verifier is linear in that count with an explicit constant. -/
theorem linear_cost (entries : List SparseEntry) (n : ℕ) (hn : n ≤ entries.length) :
    15 * entries.length + 13 * n + 27 ≤ 28 * entries.length + 27 := by omega

end Maxwell.Cost.RealSparseVerify
