import Maxwell.Cost.RealMidpointRegister.Transport
import Maxwell.Cost.RealMidpointRegister.Result

namespace Maxwell.Cost.RealMidpointRegister
open RealSparse (execute execute_add execute_sound)

/-- Input: real register 16 and precision index register 27. Output:
real register 4 and canonical magnitude, denominator, sign in indices
16, 17, 18. All buffer writes are left to the rational codec. -/
def program : Machine := ⟨[
  .literal 0 0, .literal 1 0, .literal 2 0, .literal 3 0,
  .literal 4 0, .literal 5 0, .literal 6 0, .literal 7 0,
  .indexLiteral 0 0, .indexLiteral 1 0, .indexLiteral 2 0,
  .indexLiteral 3 0, .indexLiteral 4 0, .indexLiteral 5 0] ++
  (kernel.code.map (RAMInstruction.relocate 14 70)) ++ [
  .indexCopy 16 4, .indexCopy 17 5, .branchLE 7 16 73 75,
  .indexLiteral 18 0, .jump 77, .indexLiteral 18 1, .jump 77, .halt]⟩

theorem contains_kernel : program.Contains kernel 14 70 := by
  intro i
  fin_cases i <;> rfl

noncomputable def clearFirst (s : RAMState) : RAMState :=
  ((((((s.setWord 0 0).setWord 1 0).setWord 2 0).setWord 3 0).setWord 4 0).setWord 5 0).setWord 6 0

noncomputable def cleared (s : RAMState) : RAMState :=
  (((((((clearFirst s).setWord 7 0).setIndex 0 0).setIndex 1 0).setIndex 2 0).setIndex 3 0).setIndex 4 0).setIndex 5 0

set_option maxRecDepth 20000 in
theorem clear_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (hpc : s.pc = 0) :
    execute (program.next input tape) 14 s = some (cleared s) := by
  have hfirst : execute (program.next input tape) 7 s = some (clearFirst s) := by
    simp [execute, program, Machine.next, hpc, clearFirst, RAMState.setWord]
  rw [show 14 = 7 + 7 from rfl, execute_add, hfirst, Option.bind_some]
  simp [execute, program, Machine.next, hpc, clearFirst, cleared, RAMState.setWord, RAMState.setIndex]

theorem cleared_eq (s : RAMState) (hpc : s.pc = 0) :
    cleared s = (overlay s RAMState.initial).relocate 14 := by
  simp only [cleared, clearFirst, RAMState.setWord, RAMState.setIndex, overlay,
    RAMState.initial, RAMState.relocate, hpc]
  congr 1
  · funext i
    by_cases hi : i < 8
    · interval_cases i <;> simp
    · have h0 : i ≠ 0 := by omega
      have h1 : i ≠ 1 := by omega
      have h2 : i ≠ 2 := by omega
      have h3 : i ≠ 3 := by omega
      have h4 : i ≠ 4 := by omega
      have h5 : i ≠ 5 := by omega
      have h6 : i ≠ 6 := by omega
      have h7 : i ≠ 7 := by omega
      simp [hi, h0, h1, h2, h3, h4, h5, h6, h7]
  · funext i
    by_cases hi : i < 6
    · interval_cases i <;> simp
    · have h0 : i ≠ 0 := by omega
      have h1 : i ≠ 1 := by omega
      have h2 : i ≠ 2 := by omega
      have h3 : i ≠ 3 := by omega
      have h4 : i ≠ 4 := by omega
      have h5 : i ≠ 5 := by omega
      simp [hi, h0, h1, h2, h3, h4, h5]

noncomputable def exported (s : RAMState) (x : ℝ) : RAMState :=
  let t := s.setIndex 16 (s.indices 4)
  let t := t.setIndex 17 (s.indices 5)
  let t := t.setIndex 18 (if 0 ≤ x then 0 else 1)
  {t with pc := 77}

set_option maxRecDepth 20000 in
theorem export_steps (input : RAMInput) (tape : ℕ → Bool) (s : RAMState) (x : ℝ)
    (hpc : s.pc = 70) (hz : s.words 7 = 0) (hx : s.words 16 = x) :
    execute (program.next input tape) 5 s = some (exported s x) := by
  by_cases hpos : 0 ≤ x <;>
    simp [execute, program, kernel, RealMidpoint.program, RealRound.program, adapt,
      RAMInstruction.relocate, Machine.next, hpc, hz, hx, hpos, exported, RAMState.setIndex]

end Maxwell.Cost.RealMidpointRegister
