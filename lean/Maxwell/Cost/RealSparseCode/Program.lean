import Maxwell.Cost.RealRecordCode

namespace Maxwell.Cost.RealSparseCode
open RealNatCode (Layout StoredWord)
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

noncomputable def word (rows columns : ℕ → ℕ) (values : ℕ → ℝ) (p : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 => word rows columns values p k ++ RealRecordCode.word (rows k) (columns k) (values k) p

/-- The ordered sparse stream is read from real coefficients and paired
natural coordinate arrays. Neither sorting nor input packing is hidden here. -/
def program : Machine := ⟨[
  .indexLiteral 40 0, .indexLiteral 45 1, .indexLiteral 46 2, .indexCopy 42 25, .indexCopy 43 28,
  .branchIndexLE 26 40 263 6, .loadIndex 30 43, .indexAdd 44 43 45, .loadIndex 31 44, .load 16 42] ++
  (RealRecordCode.program.code.map (RAMInstruction.relocate 10 259)) ++ [
  .indexAdd 42 42 45, .indexAdd 43 43 46, .indexAdd 40 40 45, .jump 5, .halt]⟩

theorem contains_record : program.Contains RealRecordCode.program 10 259 := by
  intro i; fin_cases i <;> rfl

structure Ready (s : RAMState) (L : Layout) (rb cb n p k : ℕ)
    (rows columns : ℕ → ℕ) (values : ℕ → ℝ) : Prop where
  pc : s.pc = 5
  count : s.indices 40 = k
  realPointer : s.indices 42 = rb + k
  coordinatePointer : s.indices 43 = cb + 2 * k
  total : s.indices 26 = n
  precision : s.indices 27 = p
  one : s.indices 45 = 1
  two : s.indices 46 = 2
  cache : s.indices 20 = L.cache
  buffer : s.indices 21 = L.bufferAt (word rows columns values p k).length
  stride : s.indices 22 = L.stride
  coefficients : ∀ j < n, s.words (rb + j) = values j
  coordinates : ∀ j < n, s.indices (cb + 2 * j) = rows j ∧ s.indices (cb + 2 * j + 1) = columns j
  stored : StoredWord s L (word rows columns values p k)

noncomputable def initialized (s : RAMState) : RAMState :=
  let t := s.setIndex 40 0
  let t := t.setIndex 45 1
  let t := t.setIndex 46 2
  let t := t.setIndex 42 (s.indices 25)
  t.setIndex 43 (s.indices 28)

theorem initialize_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 0) :
    execute (program.next input tape) 5 s = some (initialized s) := by
  simp [execute, program, Machine.next, hpc, initialized, RAMState.setIndex]

theorem initialized_ready (L : Layout) (rb cb n p : ℕ) (rows columns : ℕ → ℕ) (values : ℕ → ℝ)
    (s : RAMState) (hcb : 64 ≤ cb) (hpc : s.pc = 0) (hreal : s.indices 25 = rb)
    (hcoords : s.indices 28 = cb) (hn : s.indices 26 = n) (hp : s.indices 27 = p)
    (hc : s.indices 20 = L.cache) (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride)
    (hv : ∀ j < n, s.words (rb + j) = values j)
    (hco : ∀ j < n, s.indices (cb + 2 * j) = rows j ∧ s.indices (cb + 2 * j + 1) = columns j) :
    Ready (initialized s) L rb cb n p 0 rows columns values := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hv, ?_, ?_⟩
  all_goals try simp [initialized, RAMState.setIndex, hpc, hreal, hcoords, hn, hp, hc, hb,
    hstride, word, StoredWord, Layout.bufferAt]
  intro j hj
  have hlow : ∀ i < 64, cb + 2 * j ≠ i := by omega
  have hlow' : ∀ i < 64, cb + 2 * j + 1 ≠ i := by omega
  simpa [initialized, RAMState.setIndex, hlow, hlow'] using hco j hj

noncomputable def loaded (s : RAMState) : RAMState :=
  let t := ({s with pc := 6}).setIndex 30 (s.indices (s.indices 43))
  let t := t.setIndex 44 (s.indices 43 + 1)
  let t := t.setIndex 31 (s.indices (s.indices 43 + 1))
  t.setWord 16 (s.words (s.indices 42))

theorem load_steps (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (rb cb n p k : ℕ) (rows columns : ℕ → ℕ) (values : ℕ → ℝ) (s : RAMState)
    (hcb : 64 ≤ cb) (h : Ready s L rb cb n p k rows columns values) (hk : k < n) :
    execute (program.next input tape) 5 s = some (loaded s) := by
  have hlow : ∀ i < 64, cb + 2 * k + 1 ≠ i := by omega
  simp [execute, program, Machine.next, h.pc, h.total, h.count, show ¬ n ≤ k by omega,
    h.one, h.coordinatePointer, loaded, RAMState.setIndex, RAMState.setWord, hlow]

noncomputable def advanced (s : RAMState) : RAMState :=
  let t := s.setIndex 42 (s.indices 42 + s.indices 45)
  let t := t.setIndex 43 (s.indices 43 + s.indices 46)
  let t := t.setIndex 40 (s.indices 40 + s.indices 45)
  {t with pc := 5}

theorem advance_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 259) :
    execute (program.next input tape) 4 s = some (advanced s) := by
  simp [execute, program, RealRecordCode.program, RealNatAppend.program, RealNatCode.program,
    RealRoundRat.program, RealMidpointRegister.program, RealMidpointRegister.kernel,
    RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt, RealRatCode.program,
    RAMInstruction.relocate, Machine.next, hpc, advanced, RAMState.setIndex]

theorem outside_coordinate (L : Layout) (cb n offset i : ℕ) (hcb : 64 ≤ cb)
    (hc : cb + 2 * n ≤ L.cache) (hb : cb + 2 * n ≤ L.buffer)
    (hi : cb ≤ i) (hi' : i < cb + 2 * n) : RealNatAppend.Outside (L.shiftBuffer offset) i := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro j
    change i ≠ L.cache + L.stride * j
    omega
  · intro j
    change i ≠ L.buffer + L.stride * offset + L.stride * j
    omega

end Maxwell.Cost.RealSparseCode
