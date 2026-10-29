import Maxwell.Cost.RealRoundRat

namespace Maxwell.Cost.RealArrayCode
open RealSparse (execute execute_sound)
open RealNatCode (Layout StoredWord)
set_option maxRecDepth 20000

noncomputable def word (v : ℕ → ℝ) (p : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 => word v p k ++ Codec.rat (RealMidpoint.approximation (v k) p)

def Outside (L : Layout) (i : ℕ) : Prop :=
  29 ≤ i ∧ (∀ j, i ≠ L.cacheAt j) ∧ ∀ j, i ≠ L.bufferAt j

theorem outside_prefix (L : Layout) (offset j : ℕ) (hj : j < offset) :
    Outside (L.shiftBuffer offset) (L.bufferAt j) := by
  refine ⟨by have := L.bufferAt_ge j; omega, fun k => (L.disjoint k j).symm, ?_⟩
  intro k
  rw [Layout.shiftBuffer_bufferAt]
  intro he
  have := L.bufferAt_injective he
  omega

/-- Read a contiguous real array, round each entry, and append its actual
canonical bytes. Count and precision are runtime index registers 26 and
27; real-array cursor is 24 and bit-buffer cursor is 21. -/
def program : Machine := ⟨[
  .indexLiteral 23 0, .indexLiteral 28 1,
  .branchIndexLE 26 23 171 3, .load 16 24] ++
  (RealRoundRat.program.code.map (RAMInstruction.relocate 4 168)) ++ [
  .indexAdd 24 24 28, .indexAdd 23 23 28, .jump 2, .halt]⟩

theorem contains_round : program.Contains RealRoundRat.program 4 168 := by
  intro i
  fin_cases i <;> rfl

structure Ready (s : RAMState) (L : Layout) (base n p k : ℕ) (v : ℕ → ℝ) : Prop where
  pc : s.pc = 2
  count : s.indices 23 = k
  source : s.indices 24 = base + k
  total : s.indices 26 = n
  precision : s.indices 27 = p
  one : s.indices 28 = 1
  cache : s.indices 20 = L.cache
  buffer : s.indices 21 = L.bufferAt (word v p k).length
  stride : s.indices 22 = L.stride
  values : ∀ j < n, s.words (base + j) = v j
  stored : StoredWord s L (word v p k)

noncomputable def initialized (s : RAMState) : RAMState :=
  (s.setIndex 23 0).setIndex 28 1

theorem initialize_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 0) :
    execute (program.next input tape) 2 s = some (initialized s) := by
  simp [execute, program, Machine.next, initialized, hpc, RAMState.setIndex]

theorem initialized_ready (L : Layout) (base n p : ℕ) (v : ℕ → ℝ) (s : RAMState)
    (hpc : s.pc = 0) (hs : s.indices 24 = base) (hn : s.indices 26 = n)
    (hp : s.indices 27 = p) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride)
    (hv : ∀ j < n, s.words (base + j) = v j) : Ready (initialized s) L base n p 0 v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hv, ?_⟩
  all_goals simp [initialized, RAMState.setIndex, word, StoredWord, hpc, hs, hn, hp, hc, hb,
    hstride, Layout.bufferAt]

noncomputable def loaded (s : RAMState) : RAMState :=
  ({s with pc := 3}).setWord 16 (s.words (s.indices 24))

theorem load_steps (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (base n p k : ℕ) (v : ℕ → ℝ) (s : RAMState) (h : Ready s L base n p k v) (hk : k < n) :
    execute (program.next input tape) 2 s = some (loaded s) := by
  simp [execute, program, Machine.next, h.pc, h.total, h.count, show ¬ n ≤ k by omega, loaded]

noncomputable def advanced (s : RAMState) : RAMState :=
  let t := s.setIndex 24 (s.indices 24 + s.indices 28)
  let t := t.setIndex 23 (s.indices 23 + s.indices 28)
  {t with pc := 2}

theorem advance_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 168) :
    execute (program.next input tape) 3 s = some (advanced s) := by
  simp [execute, program, RealRoundRat.program, RealMidpointRegister.program,
    RealMidpointRegister.kernel, RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt,
    RealRatCode.program, RealNatCode.program, RAMInstruction.relocate, Machine.next, hpc,
    advanced, RAMState.setIndex]

theorem protected_prefix (L : Layout) (offset num den j : ℕ) (hj : j < offset) :
    RealRatCode.Protected (L.shiftBuffer offset) num den (L.bufferAt j) := by
  refine ⟨by have := L.bufferAt_ge j; omega, by have := L.bufferAt_ge j; omega, ?_, ?_⟩
  · intro k _; exact (L.disjoint k j).symm
  · intro k _
    rw [Layout.shiftBuffer_bufferAt]
    intro he
    have := L.bufferAt_injective he
    omega

end Maxwell.Cost.RealArrayCode
