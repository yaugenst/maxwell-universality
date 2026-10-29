import Maxwell.Cost.Model

set_option linter.unusedSimpArgs false
namespace Maxwell.Cost

structure SparseEntry where
  row : ℕ
  column : ℕ
  value : ℝ

/-- Sparse matrix-vector multiplication accumulates at the listed row.
It reads the coefficient and two vector words, multiplies and adds, then
writes back the accumulator. Empty matrix rows require no input accesses. -/
noncomputable def sparseAccumulate (vector : ℕ → ℝ) :
    List SparseEntry → (ℕ → ℝ) → Program (ℕ → ℝ)
  | [], accumulator => pure accumulator
  | e :: es, accumulator => do
      let coefficient ← perform (.read e.value)
      let coordinate ← perform (.read (vector e.column))
      let old ← perform (.read (accumulator e.row))
      let product ← perform (.multiply coefficient coordinate)
      let new ← perform (.add old product)
      perform (.write new)
      sparseAccumulate vector es (Function.update accumulator e.row new)

/-- Exactly six RAM primitives are executed for each stored coefficient,
including stored duplicates if supplied. -/
theorem sparseAccumulate_steps (vector : ℕ → ℝ) (entries : List SparseEntry)
    (accumulator : ℕ → ℝ) :
    (sparseAccumulate vector entries accumulator).steps = 6 * entries.length := by
  induction entries generalizing accumulator with
  | nil => rfl
  | cons e es ih =>
    simp [sparseAccumulate, bind, Program.bind, Program.steps, perform,
      Instruction.execute, ih]
    omega

noncomputable def sparseRowSum (entries : List SparseEntry) (vector : ℕ → ℝ)
    (row : ℕ) : ℝ :=
  (entries.map (fun e => if e.row = row then e.value * vector e.column else 0)).sum

theorem sparseAccumulate_result (vector : ℕ → ℝ) (entries : List SparseEntry)
    (accumulator : ℕ → ℝ) (row : ℕ) :
    (sparseAccumulate vector entries accumulator).result row =
      accumulator row + sparseRowSum entries vector row := by
  induction entries generalizing accumulator with
  | nil => simp [sparseAccumulate, sparseRowSum, Pure.pure]
  | cons e es ih =>
    simp only [sparseAccumulate, bind, Program.bind, perform, Program.result,
      Instruction.execute]
    rw [ih]
    simp only [sparseRowSum, List.map_cons, List.sum_cons]
    by_cases h : e.row = row
    · subst row
      simp [Function.update]
      ring
    · simp [Function.update, h, Ne.symm h]

/-- Reading only active rows is charged by the sparse scan. In particular,
there is no hidden scan over an arbitrarily padded dense source vector. -/
noncomputable def sparseMatvec (entries : List SparseEntry) (vector : ℕ → ℝ) :
    Program (ℕ → ℝ) := sparseAccumulate vector entries (fun _ => 0)

theorem sparseMatvec_result (entries : List SparseEntry) (vector : ℕ → ℝ) (row : ℕ) :
    (sparseMatvec entries vector).result row = sparseRowSum entries vector row := by
  simp [sparseMatvec, sparseAccumulate_result]

theorem sparseMatvec_steps (entries : List SparseEntry) (vector : ℕ → ℝ) :
    (sparseMatvec entries vector).steps = 6 * entries.length :=
  sparseAccumulate_steps _ _ _

/-- A finite loop visits every index, in descending order. -/
def forRange (body : ℕ → Program Unit) : ℕ → Program Unit
  | 0 => pure ()
  | n + 1 => (body n).bind (fun _ => forRange body n)

theorem forRange_steps (body : ℕ → Program Unit) (n c : ℕ)
    (h : ∀ i < n, (body i).steps = c) :
    (forRange body n).steps = n * c := by
  induction n with
  | zero => simp [forRange, Pure.pure]
  | succ n ih =>
    rw [forRange, steps_bind]
    have hn := h n (Nat.lt_succ_self n)
    rw [hn, ih (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    ring

theorem forRange_steps_le (body : ℕ → Program Unit) (n c : ℕ)
    (h : ∀ i < n, (body i).steps ≤ c) :
    (forRange body n).steps ≤ n * c := by
  induction n with
  | zero => simp [forRange, Pure.pure]
  | succ n ih =>
    rw [forRange, steps_bind]
    have hn := h n (Nat.lt_succ_self n)
    have hr := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    calc
      (body n).steps + (forRange body n).steps ≤ c + n * c := Nat.add_le_add hn hr
      _ = (n + 1) * c := by ring

/-- Complete ambient cuboid materialization, not merely defect output. -/
def forBox (nx ny nz : ℕ) (body : ℕ → ℕ → ℕ → Program Unit) : Program Unit :=
  forRange (fun x => forRange (fun y => forRange (body x y) nz) ny) nx

theorem forBox_steps (nx ny nz c : ℕ) (body : ℕ → ℕ → ℕ → Program Unit)
    (h : ∀ x < nx, ∀ y < ny, ∀ z < nz, (body x y z).steps = c) :
    (forBox nx ny nz body).steps = nx * ny * nz * c := by
  unfold forBox
  rw [forRange_steps _ nx (ny * (nz * c))]
  · ring
  · intro x hx
    apply forRange_steps
    intro y hy
    exact forRange_steps _ nz c (fun z hz => h x hx y hy z hz)

theorem forBox_steps_le (nx ny nz c : ℕ) (body : ℕ → ℕ → ℕ → Program Unit)
    (h : ∀ x < nx, ∀ y < ny, ∀ z < nz, (body x y z).steps ≤ c) :
    (forBox nx ny nz body).steps ≤ nx * ny * nz * c := by
  unfold forBox
  have hbound := forRange_steps_le _ nx (ny * (nz * c)) (by
    intro x hx
    apply forRange_steps_le
    intro y hy
    exact forRange_steps_le _ nz c (fun z hz => h x hx y hy z hz))
  convert hbound using 1
  ring

/-- The three side bounds imply the cubic volume bound at the actual
materialization loop. Routing must establish these side hypotheses. -/
theorem full_ambient_cost (nx ny nz side perCell : ℕ)
    (body : ℕ → ℕ → ℕ → Program Unit)
    (hx : nx ≤ side) (hy : ny ≤ side) (hz : nz ≤ side)
    (hbody : ∀ x < nx, ∀ y < ny, ∀ z < nz,
      (body x y z).steps ≤ perCell) :
    (forBox nx ny nz body).steps ≤ side ^ 3 * perCell := by
  apply (forBox_steps_le _ _ _ _ _ hbody).trans
  have hvol : nx * ny * nz ≤ side * side * side :=
    Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
  simpa [pow_succ] using Nat.mul_le_mul_right perCell hvol

end Maxwell.Cost
