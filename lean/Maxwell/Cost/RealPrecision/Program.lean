import Maxwell.Cost.RealSourceSerialize.Primitives

namespace Maxwell.Cost.RealPrecision
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

/-- The fixed exponent coefficient is part of the finite program. The
precision is derived from the actual record count in metadata53. -/
def program (coefficient : ℕ) : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .indexLiteral 2 1,
  .indexLiteral 27 7, .indexLiteral 3 coefficient,
  .branchIndexLE 2 53 6 10, .indexAdd 27 27 3, .indexAdd 2 2 2,
  .indexAdd 0 0 1, .jump 5, .halt]⟩

def initialized (coefficient : ℕ) (s : RAMState) : RAMState :=
  let t := s.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 2 1
  let t := t.setIndex 27 7
  t.setIndex 3 coefficient

structure Ready (coefficient n k : ℕ) (s : RAMState) : Prop where
  pc : s.pc = 5
  count : s.indices 0 = k
  one : s.indices 1 = 1
  power : s.indices 2 = 2 ^ k
  coefficient : s.indices 3 = coefficient
  precision : s.indices 27 = 7 + coefficient * k
  total : s.indices 53 = n

structure Frame (s t : RAMState) : Prop where
  words : t.words = s.words
  indices : ∀ i, 4 ≤ i → i ≠ 27 → t.indices i = s.indices i
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  randomCursor : t.randomCursor = s.randomCursor

theorem Frame.refl (s : RAMState) : Frame s s := ⟨rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
theorem Frame.trans {s t u : RAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.words.trans h.words, fun i hi hn => (k.indices i hi hn).trans (h.indices i hi hn),
    k.output.trans h.output, k.indexOutput.trans h.indexOutput, k.randomCursor.trans h.randomCursor⟩

theorem initialize_steps (coefficient : ℕ) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc = 0) :
    execute ((program coefficient).next input tape) 5 s = some (initialized coefficient s) := by
  simp [execute, program, Machine.next, hpc, initialized, RAMState.setIndex]

theorem initialized_ready (coefficient n : ℕ) (s : RAMState)
    (hpc : s.pc = 0) (hn : s.indices 53 = n) :
    Ready coefficient n 0 (initialized coefficient s) := by
  constructor <;> simp [initialized, RAMState.setIndex, hpc, hn]

theorem initialized_frame (coefficient : ℕ) (s : RAMState) : Frame s (initialized coefficient s) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro i hi hn
  simp [initialized, RAMState.setIndex, hn, show i ≠ 0 by omega,
    show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega]

def advanced (s : RAMState) : RAMState :=
  let t := s.setIndex 27 (s.indices 27 + s.indices 3)
  let t := t.setIndex 2 (s.indices 2 + s.indices 2)
  let t := t.setIndex 0 (s.indices 0 + 1)
  {t with pc := 5}

theorem cycle (coefficient n k : ℕ) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (h : Ready coefficient n k s) (hk : k < n.size) :
    execute ((program coefficient).next input tape) 5 s = some (advanced s) := by
  have hp : 2 ^ k ≤ n := Nat.lt_size.mp hk
  simp [execute, program, Machine.next, h.pc, h.total, h.power, hp, h.one,
    advanced, RAMState.setIndex]

end Maxwell.Cost.RealPrecision
