import Maxwell.Cost.RealNatCode.Buffer

namespace Maxwell.Cost.RealRatCode
open RealSparse (execute execute_add execute_sound)
open RealNatCode (Layout StoredWord)
set_option maxRecDepth 20000

/-- The source codec's sign and two canonical natural words. -/
def word (negative : Bool) (numerator denominator : ℕ) : List Bool :=
  negative :: (Codec.nat numerator ++ Codec.nat denominator)

def program : Machine := ⟨
  [.storeIndex 21 18, .indexCopy 2 16, .indexAdd 21 21 22] ++
  (RealNatCode.program.code.map (RAMInstruction.relocate 3 40)) ++
  [.indexSubtract 21 6 21, .indexAdd 21 21 6, .indexAdd 21 21 22, .indexCopy 2 17] ++
  (RealNatCode.program.code.map (RAMInstruction.relocate 44 81)) ++
  [.indexSubtract 21 6 21, .indexAdd 21 21 6, .indexAdd 21 21 22, .halt]⟩

theorem contains_numerator : program.Contains RealNatCode.program 3 40 := by
  intro i
  fin_cases i <;> rfl

theorem contains_denominator : program.Contains RealNatCode.program 44 81 := by
  intro i
  fin_cases i <;> rfl

noncomputable def started (s : RAMState) : RAMState :=
  let t := s.setIndex (s.indices 21) (s.indices 18)
  let t := t.setIndex 2 (s.indices 16)
  t.setIndex 21 (s.indices 21 + s.indices 22)

theorem start_steps (input : RAMInput) (tape : ℕ → Bool) (L : Layout) (s : RAMState)
    (hpc : s.pc = 0) (hb : s.indices 21 = L.buffer) :
    execute (program.next input tape) 3 s = some (started s) := by
  have hf : ∀ i < 256, i ≠ L.buffer := by intro i hi; have := L.buffer_ge; omega
  simp [execute, program, Machine.next, started, hpc, hb, RAMState.setIndex, hf]

/-- Reuse the completed natural codec's midpoint pointer to compute its
end address using three charged index operations. -/
noncomputable def advancedCursor (s : RAMState) : RAMState :=
  let t := s.setIndex 21 (s.indices 6 - s.indices 21)
  let t := t.setIndex 21 (s.indices 6 - s.indices 21 + s.indices 6)
  t.setIndex 21 (s.indices 6 - s.indices 21 + s.indices 6 + s.indices 22)

noncomputable def denominatorStart (s : RAMState) : RAMState :=
  (advancedCursor s).setIndex 2 (s.indices 17)

theorem bridge_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 40) :
    execute (program.next input tape) 4 s = some (denominatorStart s) := by
  simp [execute, program, RealNatCode.program, Machine.next, denominatorStart, advancedCursor,
    hpc, RAMState.setIndex]

theorem footer_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 81) :
    execute (program.next input tape) 3 s = some (advancedCursor s) := by
  simp [execute, program, RealNatCode.program, Machine.next, advancedCursor, hpc, RAMState.setIndex]

theorem cursor_formula (L : Layout) (k : ℕ) :
    L.bufferAt k - L.buffer + L.bufferAt k + L.stride = L.bufferAt (2 * k + 1) := by
  simp [Layout.bufferAt, Nat.mul_add]
  ring

@[simp] theorem started_pc (s : RAMState) : (started s).pc = s.pc + 3 := by
  simp [started, RAMState.setIndex, Nat.add_assoc]

@[simp] theorem denominatorStart_pc (s : RAMState) : (denominatorStart s).pc = s.pc + 4 := by
  simp [denominatorStart, advancedCursor, RAMState.setIndex, Nat.add_assoc]

@[simp] theorem advancedCursor_pc (s : RAMState) : (advancedCursor s).pc = s.pc + 3 := by
  simp [advancedCursor, RAMState.setIndex, Nat.add_assoc]

/-- The preparation writes the actual sign bit before either natural call. -/
theorem started_sign (L : Layout) (s : RAMState) (negative : Bool)
    (hb : s.indices 21 = L.buffer) (hs : s.indices 18 = negative.toNat) :
    StoredWord (started s) L [negative] := by
  intro j hj
  have hj0 : j = 0 := by simpa using hj
  subst j
  simp [started, RAMState.setIndex, hb, hs, Layout.bufferAt,
    show L.buffer ≠ 2 by have := L.buffer_ge; omega,
    show L.buffer ≠ 21 by have := L.buffer_ge; omega]

theorem advancedCursor_stored (L : Layout) (s : RAMState) (bits : List Bool)
    (h : StoredWord s L bits) : StoredWord (advancedCursor s) L bits := by
  intro j hj
  simpa [advancedCursor, RAMState.setIndex] using h j hj

theorem denominatorStart_stored (L : Layout) (s : RAMState) (bits : List Bool)
    (h : StoredWord s L bits) : StoredWord (denominatorStart s) L bits := by
  intro j hj
  simpa [denominatorStart, advancedCursor, RAMState.setIndex] using h j hj

end Maxwell.Cost.RealRatCode
