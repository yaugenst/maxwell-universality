import Maxwell.Cost.RealSourceSerialize.Primitives

namespace Maxwell.Cost.RealArrayCopy
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

def sign (negate : Bool) : ℝ := ((if negate then (-1 : ℚ) else 1) : ℝ)

/-- Real arrays are copied, optionally negated, by actual load/multiply/store.
Caller metadata55/56/57 supplies source base, destination base, and count. -/
def program (negate : Bool) : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .indexCopy 2 55, .indexCopy 3 56, .literal 1 (if negate then -1 else 1),
  .branchIndexLE 57 0 13 6, .load 0 2, .multiply 0 0 1, .store 3 0,
  .indexAdd 2 2 1, .indexAdd 3 3 1, .indexAdd 0 0 1, .jump 5, .halt]⟩

noncomputable def initialized (negate : Bool) (s : RAMState) : RAMState :=
  let t := s.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 2 (s.indices 55)
  let t := t.setIndex 3 (s.indices 56)
  t.setWord 1 (sign negate)

structure Frame (dst n : ℕ) (s t : RAMState) : Prop where
  words : ∀ i, 2 ≤ i → (i < dst ∨ dst + n ≤ i) → t.words i = s.words i
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

structure Ready (negate : Bool) (src dst n k : ℕ) (v : ℕ → ℝ) (s : RAMState) : Prop where
  pc : s.pc = 5
  count : s.indices 0 = k
  one : s.indices 1 = 1
  source : s.indices 2 = src + k
  target : s.indices 3 = dst + k
  total : s.indices 57 = n
  factor : s.words 1 = sign negate
  input : ∀ j < n, s.words (src + j) = v j
  output : ∀ j < k, s.words (dst + j) = sign negate * v j

theorem initialize_steps (negate : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc = 0) :
    execute ((program negate).next input tape) 5 s = some (initialized negate s) := by
  cases negate <;> simp [execute, program, Machine.next, hpc, initialized, RAMState.setIndex, RAMState.setWord, sign]

theorem initialized_ready (negate : Bool) (src dst n : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (hsrc : 8 ≤ src) (hpc : s.pc = 0) (hs : s.indices 55 = src) (hd : s.indices 56 = dst)
    (hn : s.indices 57 = n) (hv : ∀ j < n, s.words (src + j) = v j) :
    Ready negate src dst n 0 v (initialized negate s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp [initialized, RAMState.setIndex, RAMState.setWord, hpc, hs, hd, hn]
  intro j hj
  simpa [initialized, RAMState.setIndex, RAMState.setWord, show src + j ≠ 1 by omega] using hv j hj

theorem initialized_frame (negate : Bool) (dst n : ℕ) (s : RAMState) :
    Frame dst n s (initialized negate s) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro i hi _
    simp [initialized, RAMState.setIndex, RAMState.setWord, show i ≠ 1 by omega]
  · intro i hi
    simp [initialized, RAMState.setIndex, RAMState.setWord, show i ≠ 0 by omega,
      show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega]

noncomputable def advanced (s : RAMState) : RAMState :=
  let x := s.words (s.indices 2) * s.words 1
  let t := s.setWord 0 x
  let t := t.setWord (s.indices 3) x
  let t := t.setIndex 2 (s.indices 2 + 1)
  let t := t.setIndex 3 (s.indices 3 + 1)
  let t := t.setIndex 0 (s.indices 0 + 1)
  {t with pc := 5}

theorem cycle (negate : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (src dst n k : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (h : Ready negate src dst n k v s) (hk : k < n) :
    execute ((program negate).next input tape) 8 s = some (advanced s) := by
  simp [execute, program, Machine.next, h.pc, h.count, h.total, show ¬n ≤ k by omega,
    h.one, advanced, RAMState.setWord, RAMState.setIndex]

end Maxwell.Cost.RealArrayCopy
