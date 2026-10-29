import Maxwell.Cost.RealSaddleBuffer.Memory

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer)
open RealSimulation.Control
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

def appendProgram : Machine := ⟨[
  .storeIndex 7 9, .indexAdd 11 7 1, .storeIndex 11 10, .store 8 0,
  .indexAdd 7 7 2, .indexAdd 8 8 1, .halt]⟩

noncomputable def appended (s : RAMState) : RAMState :=
  let t := s.setIndex (s.indices 7) (s.indices 9)
  let t := t.setIndex 11 (s.indices 7 + 1)
  let t := t.setIndex (s.indices 7 + 1) (s.indices 10)
  let t := t.setWord (s.indices 8) (s.words 0)
  let t := t.setIndex 7 (s.indices 7 + 2)
  t.setIndex 8 (s.indices 8 + 1)

theorem append_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState)
    (hpc : s.pc = 0) (h1 : s.indices 1 = 1) (h2 : s.indices 2 = 2)
    (hc : 100 ≤ s.indices 7) (_hv : 100 ≤ s.indices 8) :
    execute (appendProgram.next input tape) 6 s = some (appended s) := by
  have hlow : ∀ i < 20, i ≠ s.indices 7 := by omega
  have hlow' : ∀ i < 20, i ≠ s.indices 7 + 1 := by omega
  simp [execute, appendProgram, Machine.next, hpc, h1, h2, appended,
    RAMState.setIndex, RAMState.setWord, hlow, hlow', show s.indices 7 ≠ 0 by omega]

theorem append_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (h1 : s.val.indices 1 = 1) (h2 : s.val.indices 2 = 2)
    (hc : 100 ≤ s.val.indices 7) (hv : 100 ≤ s.val.indices 8) :
    Executes input tape (.call appendProgram) 7 s (Store.ofState (appended s.val)) := by
  exact Executes.call appendProgram s (appended s.val) 6
    (execute_sound _ (append_steps input tape s.val s.property h1 h2 hc hv))
    (by simp [appendProgram, appended, RAMState.setIndex, RAMState.setWord, s.property])

theorem appended_register (s : RAMState) (i : ℕ) (hi : i < 100)
    (h7 : i ≠ 7) (h8 : i ≠ 8) (h11 : i ≠ 11) (hc : 100 ≤ s.indices 7) :
    (appended s).indices i = s.indices i := by
  simp [appended, RAMState.setIndex, RAMState.setWord, h7, h8, h11,
    show i ≠ s.indices 7 by omega, show i ≠ s.indices 7 + 1 by omega]

theorem appended_pointers (s : RAMState) :
    (appended s).indices 7 = s.indices 7 + 2 ∧ (appended s).indices 8 = s.indices 8 + 1 := by
  simp [appended, RAMState.setIndex]

theorem appended_written (b : Buffer) (e : SparseEntry) (s : RAMState)
    (hb : 100 ≤ b.coefficients ∧ 100 ≤ b.coordinates)
    (hc : s.indices 7 = b.coordinates) (hv : s.indices 8 = b.coefficients)
    (hr : s.indices 9 = e.row) (hcol : s.indices 10 = e.column) (he : s.words 0 = e.value) :
    Written b s (appended s) [e] := by
  have hsmall (i : ℕ) (hi : i < 20) : b.coordinates ≠ i ∧ b.coordinates + 1 ≠ i := by omega
  refine ⟨?_, ⟨?_, ?_, rfl, rfl, rfl⟩⟩
  · intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    simp [RealSparse.entryAt, Buffer.row, Buffer.column, Buffer.value, appended,
      RAMState.setIndex, RAMState.setWord, hc, hv, hr, hcol, he, hsmall]
  · intro i hi ho
    have hne : i ≠ b.coefficients := by simpa using ho
    simp [appended, RAMState.setIndex, RAMState.setWord, hv, hne]
  · intro i hi ho
    have hrow : i ≠ b.coordinates := by simp only [List.length_singleton] at ho; omega
    have hcolumn : i ≠ b.coordinates + 1 := by simp only [List.length_singleton] at ho; omega
    simp [appended, RAMState.setIndex, RAMState.setWord, hc, hrow, hcolumn,
      show i ≠ 7 by omega, show i ≠ 8 by omega, show i ≠ 11 by omega]

end Maxwell.Cost.RealSaddleBuffer
