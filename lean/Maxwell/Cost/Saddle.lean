import Maxwell.Cost.Compiler

set_option linter.unusedSimpArgs false
namespace Maxwell.Cost

/-- A sparse coordinate record is emitted as two indices and one scalar. -/
def emitEntry (entry : SparseEntry) : Program SparseEntry := do
  perform (.writeIndex entry.row)
  perform (.writeIndex entry.column)
  perform (.write entry.value)
  pure entry

@[simp] theorem emitEntry_result (entry : SparseEntry) :
    (emitEntry entry).result = entry := rfl

@[simp] theorem emitEntry_steps (entry : SparseEntry) :
    (emitEntry entry).steps = 3 := rfl

/-- The two symmetric off-diagonal records are generated from one sparse
record, sharing its coefficient. No normal matrix is ever materialized. -/
noncomputable def saddleOffDiagonal (rowCount : ℕ) :
    List SparseEntry → Program (List SparseEntry)
  | [] => pure []
  | entry :: entries => do
      let row ← perform (.readIndex entry.row)
      let column ← perform (.readIndex entry.column)
      let coefficient ← perform (.read entry.value)
      let shiftedColumn ← perform (.addIndex rowCount column)
      let upper ← emitEntry ⟨row, shiftedColumn, coefficient⟩
      let lower ← emitEntry ⟨shiftedColumn, row, coefficient⟩
      let rest ← saddleOffDiagonal rowCount entries
      pure (upper :: lower :: rest)

noncomputable def saddleOffDiagonalSpec (rowCount : ℕ) (entries : List SparseEntry) :
    List SparseEntry := entries.flatMap (fun entry =>
      [⟨entry.row, rowCount + entry.column, entry.value⟩,
       ⟨rowCount + entry.column, entry.row, entry.value⟩])

theorem saddleOffDiagonal_result (rowCount : ℕ) (entries : List SparseEntry) :
    (saddleOffDiagonal rowCount entries).result = saddleOffDiagonalSpec rowCount entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [saddleOffDiagonal, bind, Program.bind, perform, Program.result,
      Instruction.execute, emitEntry, Pure.pure, result_bind, steps_bind, result_halt, steps_halt, ih, saddleOffDiagonalSpec, List.flatMap_cons,
      List.cons_append, List.nil_append]

theorem saddleOffDiagonal_steps (rowCount : ℕ) (entries : List SparseEntry) :
    (saddleOffDiagonal rowCount entries).steps = 10 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp only [saddleOffDiagonal, bind, Program.bind, perform, Program.steps,
      Instruction.execute, emitEntry, Pure.pure, result_bind, steps_bind, result_halt, steps_halt, ih, List.length_cons]
    omega

theorem saddleOffDiagonal_length (rowCount : ℕ) (entries : List SparseEntry) :
    (saddleOffDiagonal rowCount entries).result.length = 2 * entries.length := by
  rw [saddleOffDiagonal_result]
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    simp [saddleOffDiagonalSpec] at ih ⊢
    omega

/-- A counted identity block; every padded diagonal is explicitly emitted. -/
noncomputable def identityEntries (offset : ℕ) : ℕ → Program (List SparseEntry)
  | 0 => pure []
  | n + 1 => do
      let index ← perform (.addIndex offset n)
      let entry ← emitEntry ⟨index, index, 1⟩
      let rest ← identityEntries offset n
      pure (entry :: rest)

theorem identityEntries_steps (offset n : ℕ) :
    (identityEntries offset n).steps = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [identityEntries, bind, Program.bind, perform, Program.steps,
      Instruction.execute, emitEntry, Pure.pure, result_bind, steps_bind, result_halt, steps_halt, ih]
    omega

theorem identityEntries_length (offset n : ℕ) :
    (identityEntries offset n).result.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [identityEntries, bind, Program.bind, perform, Program.result,
      Instruction.execute, emitEntry, Pure.pure, result_bind, steps_bind, result_halt, steps_halt, List.length_cons, ih]

/-- Real-RAM sparse saddle generation and explicit padding. The actual
input entries may already have been rounded; symmetric copies share the
same rounded coefficient. -/
noncomputable def compileSaddle (rows columns padding : ℕ)
    (entries : List SparseEntry) : Program (List SparseEntry) := do
  let diagonal ← identityEntries 0 rows
  let offDiagonal ← saddleOffDiagonal rows entries
  let paddingOffset ← perform (.addIndex rows columns)
  let paddingEntries ← identityEntries paddingOffset padding
  pure (diagonal ++ offDiagonal ++ paddingEntries)

theorem compileSaddle_length (rows columns padding : ℕ) (entries : List SparseEntry) :
    (compileSaddle rows columns padding entries).result.length =
      rows + 2 * entries.length + padding := by
  simp only [compileSaddle, bind, result_bind]
  change ((identityEntries 0 rows).result ++ (saddleOffDiagonal rows entries).result ++
    (identityEntries (rows + columns) padding).result).length = _
  simp [identityEntries_length, saddleOffDiagonal_length, Nat.add_assoc]

theorem compileSaddle_steps (rows columns padding : ℕ) (entries : List SparseEntry) :
    (compileSaddle rows columns padding entries).steps =
      4 * rows + 10 * entries.length + 1 + 4 * padding := by
  unfold compileSaddle
  simp only [bind, steps_bind, identityEntries_steps, saddleOffDiagonal_steps]
  change 4 * rows + (10 * entries.length + (1 + (4 * padding + 0))) = _
  omega

/-- For active rows at most `m`, padding by `m` explicitly emits between
`m` and `4m` records. This remains true before dropping rounded zeros. -/
theorem compileSaddle_record_budget (rows columns : ℕ) (entries : List SparseEntry)
    (hrows : rows ≤ entries.length) :
    entries.length ≤ (compileSaddle rows columns entries.length entries).result.length ∧
      (compileSaddle rows columns entries.length entries).result.length ≤ 4 * entries.length := by
  rw [compileSaddle_length]
  omega

end Maxwell.Cost
