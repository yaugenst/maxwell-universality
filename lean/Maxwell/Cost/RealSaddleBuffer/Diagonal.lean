import Maxwell.Cost.RealSaddleBuffer.Append

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer)
open RealSimulation.Control
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

def diagonalPrepare : Machine := ⟨[.indexCopy 9 4, .indexCopy 10 4, .literal 0 1, .halt]⟩
def diagonalFinish : Machine := ⟨[.indexAdd 4 4 1, .indexSubtract 3 3 1, .halt]⟩
def diagonalCode : Code :=
  .seq (.call diagonalPrepare) (.seq (.call appendProgram) (.call diagonalFinish))
def diagonalLoop : Code := .loop 1 3 diagonalCode

noncomputable def diagonalPrepared (s : Store) : Store :=
  Store.ofState (((s.val.setIndex 9 (s.val.indices 4)).setIndex 10 (s.val.indices 4)).setWord 0 1)
def diagonalFinished (s : Store) : Store :=
  Store.ofState ((s.val.setIndex 4 (s.val.indices 4 + 1)).setIndex 3 (s.val.indices 3 - 1))

theorem diagonalPrepare_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call diagonalPrepare) 4 s (diagonalPrepared s) := by
  apply Executes.call _ _ _ 3
  · apply execute_sound
    simp [execute, diagonalPrepare, Machine.next, s.property, RAMState.setIndex]
  · simp [diagonalPrepare, RAMState.setIndex, RAMState.setWord, s.property]

theorem diagonalFinish_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (h1 : s.val.indices 1 = 1) :
    Executes input tape (.call diagonalFinish) 3 s (diagonalFinished s) := by
  apply Executes.call _ _ _ 2
  · apply execute_sound
    simp [execute, diagonalFinish, Machine.next, s.property, h1, RAMState.setIndex]
  · simp [diagonalFinish, RAMState.setIndex, s.property]

structure DiagonalReady (b : Buffer) (s : Store) (start n : ℕ) : Prop where
  one : s.val.indices 1 = 1
  two : s.val.indices 2 = 2
  remaining : s.val.indices 3 = n
  label : s.val.indices 4 = start
  rowCursor : s.val.indices 7 = b.coordinates
  valueCursor : s.val.indices 8 = b.coefficients

theorem diagonal_cycle (input : RAMInput) (tape : ℕ → Bool) (b : Buffer)
    (start n : ℕ) (s : Store) (hb : 100 ≤ b.coefficients ∧ 100 ≤ b.coordinates)
    (h : DiagonalReady b s start (n + 1)) :
    ∃ t : Store, Executes input tape diagonalCode 14 s t ∧
      DiagonalReady (shift b 1) t (start + 1) n ∧ Written b s.val t.val [⟨start, start, 1⟩] := by
  let a := diagonalPrepared s
  let c := Store.ofState (appended a.val)
  let t := diagonalFinished c
  have ai (i : ℕ) (h9 : i ≠ 9) (h10 : i ≠ 10) : a.val.indices i = s.val.indices i := by
    simp [a, diagonalPrepared, Store.ofState, RAMState.setIndex, RAMState.setWord, h9, h10]
  have ai7 : a.val.indices 7 = b.coordinates := (ai 7 (by omega) (by omega)).trans h.rowCursor
  have ai8 : a.val.indices 8 = b.coefficients := (ai 8 (by omega) (by omega)).trans h.valueCursor
  have ca (i : ℕ) (hi : i < 7) : c.val.indices i = s.val.indices i := by
    exact (appended_register a.val i (by omega) (by omega) (by omega) (by omega)
      (by rw [ai7]; exact hb.2)).trans (ai i (by omega) (by omega))
  have hc1 : c.val.indices 1 = 1 := (ca 1 (by omega)).trans h.one
  have hw := appended_written b ⟨start, start, 1⟩ a.val hb ai7 ai8
    (by simp [a, diagonalPrepared, Store.ofState, RAMState.setIndex, RAMState.setWord, h.label])
    (by simp [a, diagonalPrepared, Store.ofState, RAMState.setIndex, RAMState.setWord, h.label])
    (by simp [a, diagonalPrepared, Store.ofState, RAMState.setWord])
  have hpointers := appended_pointers a.val
  refine ⟨t, ?_, ?_, ?_⟩
  · exact (diagonalPrepare_executes input tape s).seq
      ((append_executes input tape a ((ai 1 (by omega) (by omega)).trans h.one)
        ((ai 2 (by omega) (by omega)).trans h.two) (by rw [ai7]; exact hb.2)
        (by rw [ai8]; exact hb.1)).seq (diagonalFinish_executes input tape c hc1))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [t, diagonalFinished, Store.ofState, RAMState.setIndex] using hc1
    · simpa [t, diagonalFinished, Store.ofState, RAMState.setIndex] using (ca 2 (by omega)).trans h.two
    · simp [t, diagonalFinished, Store.ofState, RAMState.setIndex, ca 3 (by omega), h.remaining]
    · simp [t, diagonalFinished, Store.ofState, RAMState.setIndex, ca 4 (by omega), h.label]
    · simpa [t, diagonalFinished, Store.ofState, RAMState.setIndex, shift, c, ai7] using hpointers.1
    · simpa [t, diagonalFinished, Store.ofState, RAMState.setIndex, shift, c, ai8] using hpointers.2
  · refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl⟩⟩
    · intro j hj
      have hrow : b.row j ≠ 3 ∧ b.row j ≠ 4 := by dsimp [Buffer.row]; omega
      have hcol : b.column j ≠ 3 ∧ b.column j ≠ 4 := by dsimp [Buffer.column]; omega
      simpa [t, diagonalFinished, Store.ofState, RAMState.setIndex, hrow, hcol, c] using hw.stored j hj
    · intro i hi ho
      have he := hw.frame.words i hi ho
      simpa [t, diagonalFinished, c, a, diagonalPrepared, Store.ofState, RAMState.setIndex,
        RAMState.setWord, show i ≠ 0 by omega] using he
    · intro i hi ho
      have he := hw.frame.indices i hi ho
      simpa [t, diagonalFinished, c, a, diagonalPrepared, Store.ofState, RAMState.setIndex,
        RAMState.setWord, show i ≠ 3 by omega, show i ≠ 4 by omega,
        show i ≠ 9 by omega, show i ≠ 10 by omega] using he

/-- Identity or padding diagonals are emitted by a charged loop into
caller memory, with a complete frame outside the written interval. -/
theorem diagonal_executes (input : RAMInput) (tape : ℕ → Bool) (b : Buffer)
    (start n : ℕ) (s : Store) (hb : 100 ≤ b.coefficients ∧ 100 ≤ b.coordinates)
    (h : DiagonalReady b s start n) :
    ∃ t : Store, Executes input tape diagonalLoop (15 * n + 1) s t ∧
      DiagonalReady (shift b n) t (start + n) 0 ∧ Written b s.val t.val (RealSaddle.diagonal start n) := by
  induction n generalizing b start s with
  | zero =>
    refine ⟨s, Executes.done (by rw [h.one, h.remaining]; omega), ?_, Written.nil b s.val⟩
    simpa [shift] using h
  | succ n ih =>
    obtain ⟨a, hea, hra, hwa⟩ := diagonal_cycle input tape b start n s hb h
    obtain ⟨t, het, hrt, hwt⟩ := ih (shift b 1) (start + 1) a (by dsimp [shift]; omega) hra
    refine ⟨t, ?_, ?_, ?_⟩
    · convert Executes.more (by rw [h.one, h.remaining]; omega) hea het using 1 <;> try rfl
      omega
    · simpa [shift_shift, Nat.add_assoc, Nat.add_comm 1 n] using hrt
    · simpa [RealSaddle.diagonal] using hwa.append hb hwt

end Maxwell.Cost.RealSaddleBuffer
