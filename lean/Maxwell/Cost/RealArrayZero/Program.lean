import Maxwell.Cost.RealArrayCopy.Correctness

namespace Maxwell.Cost.RealArrayZero
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

/-- Caller metadata56/57 supplies the actual target base and count. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .indexCopy 3 56, .literal 0 0,
  .branchIndexLE 57 0 9 5, .store 3 0, .indexAdd 3 3 1,
  .indexAdd 0 0 1, .jump 4, .halt]⟩

noncomputable def initialized (s : RAMState) : RAMState :=
  let t := s.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 3 (s.indices 56)
  t.setWord 0 0

structure Frame (dst n : ℕ) (s t : RAMState) : Prop where
  words : ∀ i, 1 ≤ i → (i < dst ∨ dst + n ≤ i) → t.words i = s.words i
  indices : ∀ i, 4 ≤ i → t.indices i = s.indices i
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  randomCursor : t.randomCursor = s.randomCursor

theorem Frame.refl (dst n : ℕ) (s : RAMState) : Frame dst n s s :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Frame.trans {dst n : ℕ} {s t u : RAMState}
    (h : Frame dst n s t) (k : Frame dst n t u) : Frame dst n s u :=
  ⟨fun i hi ho => (k.words i hi ho).trans (h.words i hi ho),
    fun i hi => (k.indices i hi).trans (h.indices i hi), k.output.trans h.output,
    k.indexOutput.trans h.indexOutput, k.randomCursor.trans h.randomCursor⟩

structure Ready (dst n k : ℕ) (s : RAMState) : Prop where
  pc : s.pc = 4
  count : s.indices 0 = k
  one : s.indices 1 = 1
  target : s.indices 3 = dst + k
  total : s.indices 57 = n
  zero : s.words 0 = 0
  output : ∀ j < k, s.words (dst + j) = 0

theorem initialize_steps (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc = 0) :
    execute (program.next input tape) 4 s = some (initialized s) := by
  simp [execute, program, Machine.next, hpc, initialized, RAMState.setIndex, RAMState.setWord]

theorem initialized_ready (dst n : ℕ) (s : RAMState)
    (hpc : s.pc = 0) (hd : s.indices 56 = dst) (hn : s.indices 57 = n) :
    Ready dst n 0 (initialized s) := by
  constructor <;> simp [initialized, RAMState.setIndex, RAMState.setWord, hpc, hd, hn]

theorem initialized_frame (dst n : ℕ) (s : RAMState) :
    Frame dst n s (initialized s) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro i hi _
    simp [initialized, RAMState.setIndex, RAMState.setWord, show i ≠ 0 by omega]
  · intro i hi
    simp [initialized, RAMState.setIndex, RAMState.setWord, show i ≠ 0 by omega,
      show i ≠ 1 by omega, show i ≠ 3 by omega]

noncomputable def advanced (s : RAMState) : RAMState :=
  let t := s.setWord (s.indices 3) 0
  let t := t.setIndex 3 (s.indices 3 + 1)
  let t := t.setIndex 0 (s.indices 0 + 1)
  {t with pc := 4}

theorem cycle (input : RAMInput) (tape : ℕ → Bool)
    (dst n k : ℕ) (s : RAMState) (h : Ready dst n k s) (hk : k < n) :
    execute (program.next input tape) 5 s = some (advanced s) := by
  simp [execute, program, Machine.next, h.pc, h.count, h.total, show ¬n ≤ k by omega,
    h.one, h.zero, advanced, RAMState.setWord, RAMState.setIndex]

end Maxwell.Cost.RealArrayZero
