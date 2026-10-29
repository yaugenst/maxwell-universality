import Maxwell.Cost.RealNormalize

namespace Maxwell.Cost.RealArrayNormalize
open RealSparse (execute execute_add execute_sound)
open RealNormalize (maxAbs scale normalized)
set_option maxRecDepth 20000

/-- Normalize an addressed array in place. Index register25 is its base,
26 its length. The first pass computes the actual maximum and real count;
the second performs one charged division and store per nonzero-scale entry. -/
def program (byCount : Bool) : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .indexCopy 2 26, .indexLiteral 3 0,
  .indexCopy 24 25, .literal 0 0, .literal 1 0, .literal 2 0, .literal 3 (-1), .literal 4 1,
  .branchIndexLE 2 3 27 11, .load 5 24, .multiply 6 3 5, .branchLE 5 6 14 16,
  .copy 5 6, .jump 18, .copy 5 5, .jump 18,
  .branchLE 0 5 19 21, .copy 0 5, .jump 23, .copy 0 0, .jump 23,
  .add 1 1 4, .indexAdd 3 3 1, .indexAdd 24 24 1, .jump 10,
  (if byCount then .multiply 7 0 1 else .copy 7 0), .indexLiteral 3 0, .indexCopy 24 25,
  .branchIndexLE 2 3 41 31, .load 5 24, .branchLE 0 2 33 35,
  .literal 5 0, .jump 37, .divide 5 5 7, .jump 37,
  .store 24 5, .indexAdd 3 3 1, .indexAdd 24 24 1, .jump 30, .halt]⟩

structure Frame (base n : ℕ) (s t : RAMState) : Prop where
  words : ∀ i, 8 ≤ i → (i < base ∨ base + n ≤ i) → t.words i = s.words i
  indices : ∀ i, 4 ≤ i → i ≠ 24 → t.indices i = s.indices i
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  randomCursor : t.randomCursor = s.randomCursor

theorem Frame.refl (base n : ℕ) (s : RAMState) : Frame base n s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Frame.trans {base n : ℕ} {s t u : RAMState}
    (h : Frame base n s t) (k : Frame base n t u) : Frame base n s u :=
  ⟨fun i hi ho => (k.words i hi ho).trans (h.words i hi ho),
    fun i hi hn => (k.indices i hi hn).trans (h.indices i hi hn),
    k.output.trans h.output, k.indexOutput.trans h.indexOutput, k.randomCursor.trans h.randomCursor⟩

structure MaxReady (s : RAMState) (base n k : ℕ) (v : ℕ → ℝ) : Prop where
  pc : s.pc = 10
  one : s.indices 1 = 1
  total : s.indices 2 = n
  count : s.indices 3 = k
  pointer : s.indices 24 = base + k
  origin : s.indices 25 = base
  maximum : s.words 0 = maxAbs v k
  realCount : s.words 1 = k
  zero : s.words 2 = 0
  minus : s.words 3 = -1
  unit : s.words 4 = 1
  values : ∀ j < n, s.words (base + j) = v j

noncomputable def initialized (s : RAMState) : RAMState :=
  let t := s.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 2 (s.indices 26)
  let t := t.setIndex 3 0
  let t := t.setIndex 24 (s.indices 25)
  ((((t.setWord 0 0).setWord 1 0).setWord 2 0).setWord 3 (-1)).setWord 4 1

theorem initialize_steps (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc = 0) :
    execute ((program byCount).next input tape) 10 s = some (initialized s) := by
  simp [execute, program, Machine.next, initialized, hpc, RAMState.setWord, RAMState.setIndex]

theorem initialized_ready (base n : ℕ) (v : ℕ → ℝ) (s : RAMState) (hbase : 32 ≤ base)
    (hpc : s.pc = 0) (hb : s.indices 25 = base) (hn : s.indices 26 = n)
    (hv : ∀ j < n, s.words (base + j) = v j) : MaxReady (initialized s) base n 0 v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp [initialized, RAMState.setWord, RAMState.setIndex, hpc, hb, hn, maxAbs]
  intro j hj
  have hneq : ∀ i < 8, base + j ≠ i := by omega
  simpa [initialized, RAMState.setWord, RAMState.setIndex, Function.update_apply, hneq,
    show base ≠ 0 by omega] using hv j hj

theorem initialized_frame (base n : ℕ) (s : RAMState) : Frame base n s (initialized s) := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · intro i hi _
    have hn : ∀ j < 8, i ≠ j := by omega
    simp [initialized, RAMState.setWord, RAMState.setIndex, hn]
  · intro i hi hne
    have hn : ∀ j < 4, i ≠ j := by omega
    simp [initialized, RAMState.setWord, RAMState.setIndex, hn, hne]

noncomputable def maxMiddle (s : RAMState) (x : ℝ) : RAMState :=
  let t := ({s with pc := 11}).setWord 5 x
  let t := t.setWord 6 (-x)
  let t := t.setWord 5 |x|
  {t with pc := 18}

noncomputable def maxAdvanced (s : RAMState) (x : ℝ) : RAMState :=
  let t := maxMiddle s x
  let t := t.setWord 0 (max (s.words 0) |x|)
  let t := t.setWord 1 (s.words 1 + 1)
  let t := t.setIndex 3 (s.indices 3 + 1)
  let t := t.setIndex 24 (s.indices 24 + 1)
  {t with pc := 10}

end Maxwell.Cost.RealArrayNormalize
