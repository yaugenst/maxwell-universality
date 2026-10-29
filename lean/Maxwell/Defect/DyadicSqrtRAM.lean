import Maxwell.Defect.DyadicSqrt
import Maxwell.Cost.RealSparse

/-! A fixed finite Real-RAM program executing the rational dyadic-square-root
recursion. Input reads, both comparison branches, and loop control are charged. -/

namespace Maxwell.Defect.DyadicSqrt.RAM

open Maxwell.Cost Maxwell.Cost.RealSparse

set_option maxRecDepth 20000

def input (x : ℚ) (n : ℕ) : RAMInput where
  words _ := x
  indices _ := n

/-- Twenty-one instructions, independent of x and the requested precision. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .input 0 0, .inputIndex 2 0,
  .indexLiteral 1 1, .indexLiteral 3 0,
  .literal 1 0, .literal 2 1, .literal 3 (1 / 2),
  .branchIndexLE 2 3 19 9,
  .add 4 1 2, .multiply 4 4 3, .multiply 5 4 4,
  .branchLE 5 0 13 15,
  .copy 1 4, .jump 17, .copy 2 4, .jump 17,
  .indexAdd 3 3 1, .jump 8,
  .output 1, .halt]⟩

def Ready (s : RAMState) (x : ℚ) (n k : ℕ) (bounds : ℚ × ℚ) : Prop :=
  s.pc = 8 ∧ s.words 0 = (x : ℝ) ∧ s.words 1 = (bounds.1 : ℝ) ∧
    s.words 2 = (bounds.2 : ℝ) ∧ s.words 3 = (1 / 2 : ℝ) ∧
    s.indices 1 = 1 ∧ s.indices 2 = n ∧ s.indices 3 = k

noncomputable def initialized (x : ℚ) (n : ℕ) : RAMState :=
  let s := RAMState.initial.setIndex 0 0
  let s := s.setWord 0 x
  let s := s.setIndex 2 n
  let s := s.setIndex 1 1
  let s := s.setIndex 3 0
  let s := s.setWord 1 0
  let s := s.setWord 2 1
  s.setWord 3 (1 / 2)

theorem initialize_steps (x : ℚ) (n : ℕ) (tape : ℕ → Bool) :
    execute (program.next (input x n) tape) 8 RAMState.initial = some (initialized x n) := by
  simp [execute, program, Machine.next, input, initialized, RAMState.initial,
    RAMState.setIndex, RAMState.setWord]

theorem initialized_ready (x : ℚ) (n : ℕ) : Ready (initialized x n) x n 0 (interval x 0) := by
  simp [Ready, initialized, interval, RAMState.initial, RAMState.setIndex, RAMState.setWord]

noncomputable def advanced (s : RAMState) (x : ℚ) (bounds : ℚ × ℚ) : RAMState :=
  let middle := (bounds.1 + bounds.2) / 2
  let t := {s with pc := 9}
  let t := t.setWord 4 ((bounds.1 + bounds.2 : ℚ) : ℝ)
  let t := t.setWord 4 (middle : ℝ)
  let t := t.setWord 5 ((middle ^ 2 : ℚ) : ℝ)
  let t := if middle ^ 2 ≤ x then ({t with pc := 13}).setWord 1 (middle : ℝ)
    else ({t with pc := 15}).setWord 2 (middle : ℝ)
  let t := {t with pc := 17}
  let t := t.setIndex 3 (s.indices 3 + 1)
  {t with pc := 8}

set_option maxHeartbeats 1000000 in
theorem cycle (x : ℚ) (n k : ℕ) (bounds : ℚ × ℚ) (tape : ℕ → Bool)
    (s : RAMState) (hready : Ready s x n k bounds) (hk : k < n) :
    execute (program.next (input x n) tape) 9 s = some (advanced s x bounds) := by
  rcases hready with ⟨hpc, hx, ha, hb, hhalf, hone, hn, hk'⟩
  have hnot : ¬ n ≤ k := by omega
  by_cases htest : ((bounds.1 + bounds.2) / 2) ^ 2 ≤ x
  · have htest' : (((bounds.1 : ℝ) + (bounds.2 : ℝ)) / 2) ^ 2 ≤ (x : ℝ) := by exact_mod_cast htest
    simp only [pow_two, div_eq_mul_inv] at htest htest'
    simp [execute, program, Machine.next, hpc, hx, ha, hb, hhalf, hone, hn, hk', hnot,
      advanced, RAMState.setIndex, RAMState.setWord, htest, htest', pow_two, div_eq_mul_inv]
  · have htest' : ¬ (((bounds.1 : ℝ) + (bounds.2 : ℝ)) / 2) ^ 2 ≤ (x : ℝ) := by exact_mod_cast htest
    simp only [pow_two, div_eq_mul_inv] at htest htest'
    simp [execute, program, Machine.next, hpc, hx, ha, hb, hhalf, hone, hn, hk', hnot,
      advanced, RAMState.setIndex, RAMState.setWord, htest, htest', pow_two, div_eq_mul_inv]

theorem advanced_ready (s : RAMState) (x : ℚ) (n k : ℕ) (bounds : ℚ × ℚ)
    (hready : Ready s x n k bounds) :
    Ready (advanced s x bounds) x n (k + 1) (step x bounds) := by
  rcases hready with ⟨_, hx, ha, hb, hhalf, hone, hn, hk⟩
  by_cases htest : ((bounds.1 + bounds.2) / 2) ^ 2 ≤ x <;>
    simp [Ready, advanced, step, RAMState.setWord, RAMState.setIndex, htest,
      hx, ha, hb, hhalf, hone, hn, hk]

theorem advanced_output (s : RAMState) (x : ℚ) (bounds : ℚ × ℚ) :
    (advanced s x bounds).output = s.output := by
  dsimp only [advanced]
  split_ifs <;> rfl

/-- Every bisection executes exactly nine machine transitions. -/
theorem loop (x : ℚ) (n remaining k : ℕ) (tape : ℕ → Bool) (s : RAMState)
    (hready : Ready s x n k (interval x k)) (hcount : k + remaining = n) :
    ∃ final : RAMState,
      Steps (program.next (input x n) tape) (9 * remaining) s final ∧
      Ready final x n n (interval x n) ∧ final.output = s.output := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, hready, rfl⟩
  | succ remaining ih =>
    have hk : k < n := by omega
    let next := advanced s x (interval x k)
    have hsteps := execute_sound _ (cycle x n k (interval x k) tape s hready hk)
    have hnext : Ready next x n (k + 1) (interval x (k + 1)) := advanced_ready s x n k _ hready
    obtain ⟨final, hrun, hready', hout⟩ := ih (k + 1) next hnext (by omega)
    refine ⟨final, ?_, hready', hout.trans (advanced_output s x _)⟩
    convert hsteps.trans hrun using 1
    omega

noncomputable def finished (s : RAMState) : RAMState :=
  {s with pc := 20, output := s.words 1 :: s.output}

theorem finish_steps (x : ℚ) (n : ℕ) (tape : ℕ → Bool) (s : RAMState)
    (hready : Ready s x n n (interval x n)) :
    execute (program.next (input x n) tape) 2 s = some (finished s) := by
  rcases hready with ⟨hpc, _, _, _, _, _, hn, hk⟩
  simp [execute, program, Machine.next, hpc, hn, hk, finished]

theorem finished_halt (x : ℚ) (n : ℕ) (tape : ℕ → Bool) (s : RAMState) :
    program.next (input x n) tape (finished s) = none := by
  simp [program, Machine.next, finished]

/-- Exact execution of the rational recursion, with all initialization,
input, arithmetic, branch, output, and loop-control instructions charged. -/
theorem terminates (x : ℚ) (n : ℕ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      Terminates (program.next (input x n) tape) (9 * n + 10) RAMState.initial final ∧
      final.output = [(lower x n : ℝ)] := by
  have hinit := execute_sound _ (initialize_steps x n tape)
  obtain ⟨state, hloop, hready, hout⟩ := loop x n n 0 tape (initialized x n)
    (initialized_ready x n) (by omega)
  have hfinish := execute_sound _ (finish_steps x n tape state hready)
  refine ⟨finished state, ?_, ?_⟩
  · have h := (hinit.trans hloop).trans hfinish
    have ht := h.terminates (Terminates.halt _ (finished_halt x n tape state))
    convert ht using 1
    omega
  · have ha := hready.2.2.1
    simp only [finished, ha, lower]
    rw [hout]
    rfl

/-- The same actual machine computes a weight satisfying the squared
checker tolerance in a linear number of precision steps. -/
theorem weight_terminates (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (p : ℕ)
    (tape : ℕ → Bool) :
    ∃ final : RAMState,
      Terminates (program.next (input x (2 * p + 1)) tape) (18 * p + 19)
        RAMState.initial final ∧
      final.output = [(weight x p : ℝ)] ∧
      0 ≤ weight x p ∧ weight x p ≤ 1 ∧
      |weight x p ^ 2 - x| ≤ (((2 : ℚ) ^ p)⁻¹) ^ 2 := by
  obtain ⟨final, hrun, hout⟩ := terminates x (2 * p + 1) tape
  refine ⟨final, ?_, hout, weight_spec x hx hx1 p⟩
  convert hrun using 1
  omega

end Maxwell.Defect.DyadicSqrt.RAM
