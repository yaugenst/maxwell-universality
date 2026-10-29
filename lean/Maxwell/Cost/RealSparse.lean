import Maxwell.Cost.Machine
import Maxwell.Cost.Execution
import Maxwell.Cost.Compiler

/-! A fixed finite Real-RAM sparse transpose product. Coefficients and
vector coordinates are read from the real input tape; sparse row and column
indices are read from the natural input tape. Every access and arithmetic
operation is an actual instruction of the finite machine. -/

namespace Maxwell.Cost.RealSparse

set_option maxRecDepth 20000

noncomputable def entryAt (entries : List SparseEntry) (k : ℕ) : SparseEntry :=
  entries[k]?.getD ⟨0, 0, 0⟩

/-- The index tape contains the entry count, then row/column pairs. The
real tape contains all coefficients followed by the input vector. -/
noncomputable def input (entries : List SparseEntry) (vector : ℕ → ℝ) : RAMInput where
  words a := if a < entries.length then (entryAt entries a).value else vector (a - entries.length)
  indices a := if a = 0 then entries.length else
    if (a - 1) % 2 = 0 then (entryAt entries ((a - 1) / 2)).row
    else (entryAt entries ((a - 1) / 2)).column

@[simp] theorem input_count (entries : List SparseEntry) (vector : ℕ → ℝ) :
    (input entries vector).indices 0 = entries.length := by simp [input]

theorem input_row (entries : List SparseEntry) (vector : ℕ → ℝ) (k : ℕ) :
    (input entries vector).indices (1 + 2 * k) = (entryAt entries k).row := by
  simp [input, Nat.mul_comm]

theorem input_column (entries : List SparseEntry) (vector : ℕ → ℝ) (k : ℕ) :
    (input entries vector).indices (2 + 2 * k) = (entryAt entries k).column := by
  have hsub : 2 + 2 * k - 1 = 2 * k + 1 := by omega
  simp [input, hsub, Nat.add_div, Nat.add_mod]

theorem input_value (entries : List SparseEntry) (vector : ℕ → ℝ) (k : ℕ)
    (hk : k < entries.length) :
    (input entries vector).words k = (entryAt entries k).value := by simp [input, hk]

theorem input_vector (entries : List SparseEntry) (vector : ℕ → ℝ) (row : ℕ) :
    (input entries vector).words (entries.length + row) = vector row := by simp [input]

/-- Twenty-two fixed instructions, independent of the sparse input size. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .inputIndex 2 0,
  .indexLiteral 3 0, .indexLiteral 4 1, .indexLiteral 10 16,
  .branchIndexLE 2 3 21 7,
  .inputIndex 5 4, .indexAdd 4 4 1, .inputIndex 6 4,
  .input 0 3, .indexAdd 7 2 5, .input 1 7,
  .indexAdd 8 10 6, .load 2 8, .multiply 3 0 1,
  .add 2 2 3, .store 8 2,
  .indexAdd 3 3 1, .indexAdd 4 4 1, .jump 6, .halt]⟩

def execute {σ : Type} (next : σ → Option σ) : ℕ → σ → Option σ
  | 0, s => some s
  | k + 1, s => (next s).bind (execute next k)

theorem execute_add {σ : Type} (next : σ → Option σ) (a b : ℕ) (s : σ) :
    execute next (a + b) s = (execute next a s).bind (execute next b) := by
  induction a generalizing s with
  | zero => simp [execute]
  | succ a ih =>
    rw [Nat.succ_add, execute]
    cases h : next s with
    | none => simp [execute, h]
    | some t => simp [execute, h, ih]

theorem execute_sound {σ : Type} (next : σ → Option σ) {n : ℕ} {s t : σ}
    (h : execute next n s = some t) : Steps next n s t := by
  induction n generalizing s with
  | zero => simp only [execute, Option.some.injEq] at h; subst t; exact Steps.refl _
  | succ n ih =>
    cases hn : next s with
    | none => simp [execute, hn] at h
    | some u =>
      have hu : execute next n u = some t := by simpa only [execute, hn, Option.bind_some] using h
      exact Steps.step hn (ih hu)

def Ready (s : RAMState) (m k : ℕ) : Prop :=
  s.pc = 6 ∧ s.indices 0 = 0 ∧ s.indices 1 = 1 ∧ s.indices 2 = m ∧
    s.indices 3 = k ∧ s.indices 4 = 1 + 2 * k ∧ s.indices 10 = 16

noncomputable def initialized (m : ℕ) : RAMState :=
  (((((RAMState.initial.setIndex 0 0).setIndex 1 1).setIndex 2 m).setIndex 3 0).setIndex 4 1).setIndex 10 16

theorem initialize_steps (entries : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    execute (program.next (input entries vector) tape) 6 RAMState.initial =
      some (initialized entries.length) := by
  simp [execute, program, Machine.next, RAMState.initial, RAMState.setIndex, initialized, input]

theorem initialized_ready (m : ℕ) : Ready (initialized m) m 0 := by
  simp [Ready, initialized, RAMState.setIndex, RAMState.initial]

noncomputable def advanced (s : RAMState) (entry : SparseEntry) (x : ℝ) : RAMState :=
  let t := {s with pc := 7}
  let t := t.setIndex 5 entry.row
  let t := t.setIndex 4 (s.indices 4 + 1)
  let t := t.setIndex 6 entry.column
  let t := t.setWord 0 entry.value
  let t := t.setIndex 7 (s.indices 2 + entry.row)
  let t := t.setWord 1 x
  let t := t.setIndex 8 (16 + entry.column)
  let t := t.setWord 2 (s.words (16 + entry.column))
  let t := t.setWord 3 (entry.value * x)
  let t := t.setWord 2 (s.words (16 + entry.column) + entry.value * x)
  let t := t.setWord (16 + entry.column) (s.words (16 + entry.column) + entry.value * x)
  let t := t.setIndex 3 (s.indices 3 + 1)
  let t := t.setIndex 4 (s.indices 4 + 2)
  {t with pc := 6}

noncomputable def middle (s : RAMState) (e : SparseEntry) (x : ℝ) : RAMState :=
  let t := {s with pc := 7}
  let t := t.setIndex 5 e.row
  let t := t.setIndex 4 (s.indices 4 + 1)
  let t := t.setIndex 6 e.column
  let t := t.setWord 0 e.value
  let t := t.setIndex 7 (s.indices 2 + e.row)
  t.setWord 1 x

set_option maxHeartbeats 1400000 in
theorem cycle (entries : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool)
    (s : RAMState) (k : ℕ) (hready : Ready s entries.length k) (hk : k < entries.length) :
    execute (program.next (input entries vector) tape) 15 s =
      some (advanced s (entryAt entries k) (vector (entryAt entries k).row)) := by
  rcases hready with ⟨hpc, _, h1, hm, hi, ha, hb⟩
  have hnot : ¬ entries.length ≤ k := by omega
  have haddr : 1 + 2 * k + 1 = 2 + 2 * k := by omega
  have hlarge : ∀ j : ℕ, 16 + j ≠ 0 ∧ 16 + j ≠ 1 ∧ 16 + j ≠ 2 ∧ 16 + j ≠ 3 := by omega
  have hfirst : execute (program.next (input entries vector) tape) 7 s =
      some (middle s (entryAt entries k) (vector (entryAt entries k).row)) := by
    simp (config := { maxSteps := 100000 }) [execute, program, Machine.next,
      hpc, h1, hm, hi, ha, hnot, RAMState.setWord, RAMState.setIndex,
      input_row, input_column, input_value, input_vector, hk, haddr, middle]
  rw [show 15 = 7 + 8 from rfl, execute_add, hfirst, Option.bind_some]
  simp (config := { maxSteps := 100000 }) [execute, program, Machine.next,
    h1, hm, hi, ha, hb, RAMState.setWord, RAMState.setIndex,
    hlarge, middle, advanced, Nat.add_assoc]

theorem advanced_ready (s : RAMState) (m k : ℕ) (h : Ready s m k) (entry : SparseEntry) (x : ℝ) :
    Ready (advanced s entry x) m (k + 1) := by
  rcases h with ⟨hpc, h0, h1, hm, hi, ha, hb⟩
  simp [Ready, advanced, RAMState.setWord, RAMState.setIndex, h0, h1, hm, hi, ha, hb]
  omega

theorem advanced_memory (s : RAMState) (entry : SparseEntry) (x : ℝ) (j : ℕ) :
    (advanced s entry x).words (16 + j) =
      s.words (16 + j) + if entry.column = j then entry.value * x else 0 := by
  have hlarge : 16 + j ≠ 0 ∧ 16 + j ≠ 1 ∧ 16 + j ≠ 2 ∧ 16 + j ≠ 3 := by omega
  by_cases hj : entry.column = j
  · subst j
    simp [advanced, RAMState.setWord, RAMState.setIndex]
  · simp [advanced, RAMState.setWord, RAMState.setIndex, Function.update, hlarge, hj, Ne.symm hj]

theorem advanced_frame (s : RAMState) (entry : SparseEntry) (x : ℝ) :
    (advanced s entry x).randomCursor = s.randomCursor ∧ (advanced s entry x).output = s.output := by
  exact ⟨rfl, rfl⟩

noncomputable def contribution (entries : List SparseEntry) (vector : ℕ → ℝ) (k j : ℕ) : ℝ :=
  if (entryAt entries k).column = j then (entryAt entries k).value * vector (entryAt entries k).row else 0

theorem loop (entries : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (hready : Ready s entries.length k)
    (hcount : k + remaining = entries.length) :
    ∃ final : RAMState,
      Terminates (program.next (input entries vector) tape) (15 * remaining + 1) s final ∧
      final.pc = 21 ∧
      (∀ j, final.words (16 + j) = s.words (16 + j) +
        ∑ i ∈ Finset.range remaining, contribution entries vector (k + i) j) ∧
      final.randomCursor = s.randomCursor ∧ final.output = s.output := by
  induction remaining generalizing k s with
  | zero =>
    let final : RAMState := {s with pc := 21}
    refine ⟨final, ?_, rfl, ?_, rfl, rfl⟩
    · have hstep : program.next (input entries vector) tape s = some final := by
        rcases hready with ⟨hpc, _, _, hm, hi, _, _⟩
        have hle : entries.length ≤ k := by omega
        simp [program, Machine.next, hpc, hm, hi, hle, final]
      exact Terminates.step hstep (Terminates.halt final (by simp [program, Machine.next, final]))
    · intro j
      simp [final]
  | succ remaining ih =>
    have hk : k < entries.length := by omega
    let next := advanced s (entryAt entries k) (vector (entryAt entries k).row)
    have hsteps := execute_sound _ (cycle entries vector tape s k hready hk)
    obtain ⟨final, hrun, hpc, hmemory, hrandom, hout⟩ := ih next (k + 1)
      (advanced_ready s _ k hready _ _) (by omega)
    refine ⟨final, ?_, hpc, ?_, hrandom, hout⟩
    · convert hsteps.terminates hrun using 1
      omega
    · intro j
      rw [hmemory, advanced_memory]
      rw [Finset.sum_range_succ']
      simp only [Nat.add_zero, contribution]
      have he : (∑ i ∈ Finset.range remaining,
          if (entryAt entries (k + 1 + i)).column = j then
            (entryAt entries (k + 1 + i)).value * vector (entryAt entries (k + 1 + i)).row else 0) =
        ∑ i ∈ Finset.range remaining,
          if (entryAt entries (k + (i + 1))).column = j then
            (entryAt entries (k + (i + 1))).value * vector (entryAt entries (k + (i + 1))).row else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        have hki : k + 1 + i = k + (i + 1) := by omega
        rw [hki]
      rw [he]
      ring

/-- The mathematical sparse transpose sum includes every stored entry,
including duplicate coordinates, exactly once. -/
noncomputable def transposeSum (entries : List SparseEntry) (vector : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range entries.length, contribution entries vector k j

/-- The rectangular matrix represented by the same sparse records. This
definition is a correctness specification, never a machine instruction. -/
noncomputable def rectangularMatrix (rows columns : ℕ) (entries : List SparseEntry) :
    Matrix (Fin rows) (Fin columns) ℝ := fun i j =>
  ∑ k ∈ Finset.range entries.length,
    if (entryAt entries k).row = i.val ∧ (entryAt entries k).column = j.val then
      (entryAt entries k).value else 0

noncomputable def vectorInput {rows : ℕ} (x : Fin rows → ℝ) (i : ℕ) : ℝ :=
  if hi : i < rows then x ⟨i, hi⟩ else 0

theorem transposeSum_eq_mulVec (rows columns : ℕ) (entries : List SparseEntry)
    (hrows : ∀ k < entries.length, (entryAt entries k).row < rows)
    (x : Fin rows → ℝ) (j : Fin columns) :
    transposeSum entries (vectorInput x) j.val =
      (rectangularMatrix rows columns entries).transpose.mulVec x j := by
  classical
  unfold transposeSum Matrix.mulVec dotProduct
  simp only [Matrix.transpose_apply, rectangularMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hrow := hrows k (Finset.mem_range.mp hk)
  let i : Fin rows := ⟨(entryAt entries k).row, hrow⟩
  rw [Finset.sum_eq_single i]
  · simp [contribution, vectorInput, hrow, i, ite_mul]
  · intro t _ hti
    have hne : (entryAt entries k).row ≠ t.val := by
      intro he
      apply hti
      apply Fin.ext
      exact he.symm
    simp [hne]
  · simp

/-- The fixed machine actually computes the sparse transpose product.
The exact cost includes initialization, every loop test, and loop exit. -/
theorem terminates (entries : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      Terminates (program.next (input entries vector) tape) (15 * entries.length + 7)
        RAMState.initial final ∧
      (∀ j, final.words (16 + j) = transposeSum entries vector j) ∧
      final.randomCursor = 0 ∧ final.output = [] := by
  have hinit := execute_sound _ (initialize_steps entries vector tape)
  obtain ⟨final, hrun, _, hmem, hrandom, hout⟩ := loop entries vector tape entries.length
    (initialized entries.length) 0 (initialized_ready _) (by omega)
  refine ⟨final, ?_, ?_, hrandom, hout⟩
  · convert hinit.terminates hrun using 1
    omega
  · intro j
    simpa [initialized, RAMState.setIndex, RAMState.initial, transposeSum] using hmem j

/-- The operational time cap returns this same computed result. -/
theorem run (entries : List SparseEntry) (vector : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      (program.run (input entries vector) tape (15 * entries.length + 8)).finished = some final ∧
      (program.run (input entries vector) tape (15 * entries.length + 8)).instructions =
        15 * entries.length + 7 ∧
      (∀ j, final.words (16 + j) = transposeSum entries vector j) ∧ final.randomCursor = 0 := by
  obtain ⟨final, hrun, hmem, hrandom, _⟩ := terminates entries vector tape
  have hcap := runCapped_of_terminates _ hrun
  exact ⟨final, hcap.1, hcap.2, hmem, hrandom⟩

/-- All widths of a rectangular sparse input are supported by the same
finite program. Sparse duplicate records are interpreted additively. -/
theorem rectangular_run (rows columns : ℕ) (entries : List SparseEntry)
    (hrows : ∀ k < entries.length, (entryAt entries k).row < rows)
    (x : Fin rows → ℝ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      (program.run (input entries (vectorInput x)) tape (15 * entries.length + 8)).finished = some final ∧
      (program.run (input entries (vectorInput x)) tape (15 * entries.length + 8)).instructions =
        15 * entries.length + 7 ∧
      (∀ j : Fin columns, final.words (16 + j.val) =
        (rectangularMatrix rows columns entries).transpose.mulVec x j) := by
  obtain ⟨final, hrun, hcost, hmem, _⟩ := run entries (vectorInput x) tape
  refine ⟨final, hrun, hcost, ?_⟩
  intro j
  rw [hmem, transposeSum_eq_mulVec rows columns entries hrows x j]

end Maxwell.Cost.RealSparse
