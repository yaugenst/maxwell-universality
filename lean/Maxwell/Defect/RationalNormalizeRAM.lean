import Maxwell.Defect.RationalNormalize
import Maxwell.Defect.DyadicSqrtRAM

/-! Fixed finite Real-RAM normalization: sum squares, bisect a scaled
square root, and divide every coordinate by the upper norm enclosure. -/

namespace Maxwell.Defect.RationalNormalize.RAM

open Maxwell.Cost Maxwell.Cost.RealSparse

set_option maxRecDepth 20000

def sumSquare (v : ℕ → ℚ) (n : ℕ) : ℚ := ∑ j ∈ Finset.range n, v j ^ 2

def scaledSquare (v : ℕ → ℚ) (B : ℚ) (n : ℕ) : ℚ := sumSquare v n / B ^ 2

def normUpper (v : ℕ → ℚ) (B : ℚ) (n p : ℕ) : ℚ :=
  B * DyadicSqrt.upper (scaledSquare v B n) p

def input (v : ℕ → ℚ) (B : ℚ) (n p : ℕ) : RAMInput where
  words a := if a = 0 then B else v (a - 1)
  indices a := if a = 0 then n else p

@[simp] theorem input_value (v : ℕ → ℚ) (B : ℚ) (n p k : ℕ) :
    (input v B n p).words (k + 1) = (v k : ℝ) := by simp [input]

/-- Forty-one fixed instructions. The code is independent of dimension,
precision, vector entries, and norm bounds. -/
def program : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .inputIndex 2 0, .inputIndex 3 1,
  .input 0 0, .literal 1 0, .indexLiteral 4 0,
  .branchIndexLE 2 4 14 8,
  .indexAdd 5 4 1, .input 2 5, .multiply 2 2 2, .add 1 1 2,
  .indexAdd 4 4 1, .jump 7,
  .multiply 3 0 0, .divide 1 1 3, .literal 2 0, .literal 3 1,
  .literal 4 (1 / 2), .indexLiteral 4 0,
  .branchIndexLE 3 4 31 21,
  .add 5 2 3, .multiply 5 5 4, .multiply 6 5 5,
  .branchLE 6 1 25 27, .copy 2 5, .jump 29, .copy 3 5, .jump 29,
  .indexAdd 4 4 1, .jump 20,
  .multiply 3 0 3, .indexLiteral 4 0,
  .branchIndexLE 2 4 40 34,
  .indexAdd 5 4 1, .input 2 5, .divide 2 2 3, .output 2,
  .indexAdd 4 4 1, .jump 33, .halt]⟩

def SumReady (s : RAMState) (v : ℕ → ℚ) (B : ℚ) (n p k : ℕ) : Prop :=
  s.pc = 7 ∧ s.indices 1 = 1 ∧ s.indices 2 = n ∧ s.indices 3 = p ∧
    s.indices 4 = k ∧ s.words 0 = (B : ℝ) ∧ s.words 1 = (sumSquare v k : ℝ) ∧ s.output = []

noncomputable def initialized (B : ℚ) (n p : ℕ) : RAMState :=
  let s := RAMState.initial.setIndex 0 0
  let s := s.setIndex 1 1
  let s := s.setIndex 2 n
  let s := s.setIndex 3 p
  let s := s.setWord 0 B
  let s := s.setWord 1 0
  s.setIndex 4 0

theorem initialize_steps (v : ℕ → ℚ) (B : ℚ) (n p : ℕ) (tape : ℕ → Bool) :
    execute (program.next (input v B n p) tape) 7 RAMState.initial = some (initialized B n p) := by
  simp [execute, program, Machine.next, input, initialized, RAMState.initial,
    RAMState.setIndex, RAMState.setWord]

theorem initialized_ready (v : ℕ → ℚ) (B : ℚ) (n p : ℕ) :
    SumReady (initialized B n p) v B n p 0 := by
  simp [SumReady, initialized, sumSquare, RAMState.initial, RAMState.setIndex, RAMState.setWord]

noncomputable def sumAdvanced (s : RAMState) (v : ℕ → ℚ) (k : ℕ) : RAMState :=
  let t := {s with pc := 8}
  let t := t.setIndex 5 (k + 1)
  let t := t.setWord 2 (v k : ℝ)
  let t := t.setWord 2 ((v k ^ 2 : ℚ) : ℝ)
  let t := t.setWord 1 (s.words 1 + ((v k ^ 2 : ℚ) : ℝ))
  let t := t.setIndex 4 (k + 1)
  {t with pc := 7}

set_option maxHeartbeats 1000000 in
theorem sum_cycle (v : ℕ → ℚ) (B : ℚ) (n p k : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : SumReady s v B n p k) (hk : k < n) :
    execute (program.next (input v B n p) tape) 7 s = some (sumAdvanced s v k) := by
  rcases hready with ⟨hpc, h1, hn, _, hk', _, _, _⟩
  have hnot : ¬ n ≤ k := by omega
  simp [execute, program, Machine.next, hpc, h1, hn, hk', hnot,
    sumAdvanced, RAMState.setIndex, RAMState.setWord, pow_two]

theorem sumAdvanced_ready (s : RAMState) (v : ℕ → ℚ) (B : ℚ) (n p k : ℕ)
    (hready : SumReady s v B n p k) : SumReady (sumAdvanced s v k) v B n p (k + 1) := by
  rcases hready with ⟨_, h1, hn, hp, _, hB, hsum, hout⟩
  simp [SumReady, sumAdvanced, RAMState.setWord, RAMState.setIndex, h1, hn, hp,
    hB, hsum, hout, sumSquare, Finset.sum_range_succ]

theorem sum_loop (v : ℕ → ℚ) (B : ℚ) (n p remaining k : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : SumReady s v B n p k) (hcount : k + remaining = n) :
    ∃ final : RAMState, Steps (program.next (input v B n p) tape) (7 * remaining) s final ∧
      SumReady final v B n p n := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, hready⟩
  | succ remaining ih =>
    have hk : k < n := by omega
    have hsteps := execute_sound _ (sum_cycle v B n p k tape s hready hk)
    obtain ⟨final, hrun, hready'⟩ := ih (k + 1) (sumAdvanced s v k)
      (sumAdvanced_ready s v B n p k hready) (by omega)
    refine ⟨final, ?_, hready'⟩
    convert hsteps.trans hrun using 1
    omega

def BisectReady (s : RAMState) (v : ℕ → ℚ) (B : ℚ) (n p k : ℕ) : Prop :=
  s.pc = 20 ∧ s.indices 1 = 1 ∧ s.indices 2 = n ∧ s.indices 3 = p ∧ s.indices 4 = k ∧
    s.words 0 = (B : ℝ) ∧ s.words 1 = (scaledSquare v B n : ℝ) ∧
    s.words 2 = ((DyadicSqrt.interval (scaledSquare v B n) k).1 : ℝ) ∧
    s.words 3 = ((DyadicSqrt.interval (scaledSquare v B n) k).2 : ℝ) ∧
    s.words 4 = (1 / 2 : ℝ) ∧ s.output = []

noncomputable def bisectInitialized (s : RAMState) (v : ℕ → ℚ) (B : ℚ) (n : ℕ) : RAMState :=
  let t := {s with pc := 14}
  let t := t.setWord 3 ((B ^ 2 : ℚ) : ℝ)
  let t := t.setWord 1 (scaledSquare v B n : ℝ)
  let t := t.setWord 2 0
  let t := t.setWord 3 1
  let t := t.setWord 4 (1 / 2)
  t.setIndex 4 0

theorem bisect_initialize_steps (v : ℕ → ℚ) (B : ℚ) (n p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : SumReady s v B n p n) :
    execute (program.next (input v B n p) tape) 7 s = some (bisectInitialized s v B n) := by
  rcases hready with ⟨hpc, _, hn, _, hk, hB, hsum, _⟩
  simp [execute, program, Machine.next, hpc, hn, hk, hB, hsum, bisectInitialized,
    scaledSquare, RAMState.setIndex, RAMState.setWord, pow_two]

theorem bisectInitialized_ready (s : RAMState) (v : ℕ → ℚ) (B : ℚ) (n p : ℕ)
    (hready : SumReady s v B n p n) : BisectReady (bisectInitialized s v B n) v B n p 0 := by
  rcases hready with ⟨_, h1, hn, hp, _, hB, _, hout⟩
  simp [BisectReady, bisectInitialized, DyadicSqrt.interval, RAMState.setIndex,
    RAMState.setWord, h1, hn, hp, hB, hout]

noncomputable def bisectAdvanced (s : RAMState) (x : ℚ) (bounds : ℚ × ℚ) (k : ℕ) : RAMState :=
  let middle := (bounds.1 + bounds.2) / 2
  let t := {s with pc := 21}
  let t := t.setWord 5 ((bounds.1 + bounds.2 : ℚ) : ℝ)
  let t := t.setWord 5 (middle : ℝ)
  let t := t.setWord 6 ((middle ^ 2 : ℚ) : ℝ)
  let t := if middle ^ 2 ≤ x then ({t with pc := 25}).setWord 2 (middle : ℝ)
    else ({t with pc := 27}).setWord 3 (middle : ℝ)
  let t := {t with pc := 29}
  let t := t.setIndex 4 (k + 1)
  {t with pc := 20}

set_option maxHeartbeats 1000000 in
theorem bisect_cycle (v : ℕ → ℚ) (B : ℚ) (n p k : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : BisectReady s v B n p k) (hk : k < p) :
    execute (program.next (input v B n p) tape) 9 s =
      some (bisectAdvanced s (scaledSquare v B n) (DyadicSqrt.interval (scaledSquare v B n) k) k) := by
  rcases hready with ⟨hpc, h1, _, hp, hk', _, hx, ha, hb, hhalf, _⟩
  have hnot : ¬ p ≤ k := by omega
  let bounds := DyadicSqrt.interval (scaledSquare v B n) k
  change s.words 2 = (bounds.1 : ℝ) at ha
  change s.words 3 = (bounds.2 : ℝ) at hb
  by_cases htest : ((bounds.1 + bounds.2) / 2) ^ 2 ≤ scaledSquare v B n
  · have htest' : (((bounds.1 : ℝ) + (bounds.2 : ℝ)) / 2) ^ 2 ≤ (scaledSquare v B n : ℝ) := by exact_mod_cast htest
    simp only [pow_two, div_eq_mul_inv] at htest htest'
    change _ = some (bisectAdvanced s (scaledSquare v B n) bounds k)
    simp [execute, program, Machine.next, hpc, h1, hp, hk', hx, ha, hb, hhalf, hnot,
      bisectAdvanced, RAMState.setIndex, RAMState.setWord, htest, htest', pow_two, div_eq_mul_inv]
  · have htest' : ¬ (((bounds.1 : ℝ) + (bounds.2 : ℝ)) / 2) ^ 2 ≤ (scaledSquare v B n : ℝ) := by exact_mod_cast htest
    simp only [pow_two, div_eq_mul_inv] at htest htest'
    change _ = some (bisectAdvanced s (scaledSquare v B n) bounds k)
    simp [execute, program, Machine.next, hpc, h1, hp, hk', hx, ha, hb, hhalf, hnot,
      bisectAdvanced, RAMState.setIndex, RAMState.setWord, htest, htest', pow_two, div_eq_mul_inv]

theorem bisectAdvanced_ready (s : RAMState) (v : ℕ → ℚ) (B : ℚ) (n p k : ℕ)
    (hready : BisectReady s v B n p k) :
    BisectReady (bisectAdvanced s (scaledSquare v B n) (DyadicSqrt.interval (scaledSquare v B n) k) k)
      v B n p (k + 1) := by
  rcases hready with ⟨_, h1, hn, hp, hk, hB, hx, ha, hb, hhalf, hout⟩
  let bounds := DyadicSqrt.interval (scaledSquare v B n) k
  by_cases htest : ((bounds.1 + bounds.2) / 2) ^ 2 ≤ scaledSquare v B n <;>
    simp [BisectReady, bisectAdvanced, DyadicSqrt.interval, DyadicSqrt.step, RAMState.setWord,
      RAMState.setIndex, htest, bounds, h1, hn, hp, hk, hB, hx, ha, hb, hhalf, hout] at *

theorem bisect_loop (v : ℕ → ℚ) (B : ℚ) (n p remaining k : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : BisectReady s v B n p k) (hcount : k + remaining = p) :
    ∃ final : RAMState, Steps (program.next (input v B n p) tape) (9 * remaining) s final ∧
      BisectReady final v B n p p := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k = p := by omega
    subst k
    exact ⟨s, Steps.refl s, hready⟩
  | succ remaining ih =>
    have hk : k < p := by omega
    have hsteps := execute_sound _ (bisect_cycle v B n p k tape s hready hk)
    obtain ⟨final, hrun, hready'⟩ := ih (k + 1)
      (bisectAdvanced s (scaledSquare v B n) (DyadicSqrt.interval (scaledSquare v B n) k) k)
      (bisectAdvanced_ready s v B n p k hready) (by omega)
    refine ⟨final, ?_, hready'⟩
    convert hsteps.trans hrun using 1
    omega

def outputPrefix (v : ℕ → ℚ) (divisor : ℚ) : ℕ → List ℝ
  | 0 => []
  | k + 1 => (v k / divisor : ℚ) :: outputPrefix v divisor k

def OutputReady (s : RAMState) (v : ℕ → ℚ) (divisor : ℚ) (n k : ℕ) : Prop :=
  s.pc = 33 ∧ s.indices 1 = 1 ∧ s.indices 2 = n ∧ s.indices 4 = k ∧
    s.words 3 = (divisor : ℝ) ∧ s.output = outputPrefix v divisor k

noncomputable def outputInitialized (s : RAMState) (divisor : ℚ) : RAMState :=
  let t := {s with pc := 31}
  let t := t.setWord 3 (divisor : ℝ)
  t.setIndex 4 0

theorem output_initialize_steps (v : ℕ → ℚ) (B : ℚ) (n p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : BisectReady s v B n p p) :
    execute (program.next (input v B n p) tape) 3 s = some (outputInitialized s (normUpper v B n p)) := by
  rcases hready with ⟨hpc, _, _, hp, hk, hB, _, _, hu, _, _⟩
  simp [execute, program, Machine.next, hpc, hp, hk, hB, hu, normUpper, DyadicSqrt.upper,
    outputInitialized, RAMState.setIndex, RAMState.setWord]

theorem outputInitialized_ready (s : RAMState) (v : ℕ → ℚ) (B : ℚ) (n p : ℕ)
    (hready : BisectReady s v B n p p) :
    OutputReady (outputInitialized s (normUpper v B n p)) v (normUpper v B n p) n 0 := by
  rcases hready with ⟨_, h1, hn, _, _, _, _, _, _, _, hout⟩
  simp [OutputReady, outputInitialized, RAMState.setIndex, RAMState.setWord, h1, hn, hout, outputPrefix]

noncomputable def outputAdvanced (s : RAMState) (v : ℕ → ℚ) (divisor : ℚ) (k : ℕ) : RAMState :=
  let t := {s with pc := 34}
  let t := t.setIndex 5 (k + 1)
  let t := t.setWord 2 (v k : ℝ)
  let t := t.setWord 2 ((v k / divisor : ℚ) : ℝ)
  let t := {t with pc := 38, output := (v k / divisor : ℚ) :: s.output}
  let t := t.setIndex 4 (k + 1)
  {t with pc := 33}

theorem output_cycle (v : ℕ → ℚ) (B divisor : ℚ) (n p k : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : OutputReady s v divisor n k) (hk : k < n) :
    execute (program.next (input v B n p) tape) 7 s = some (outputAdvanced s v divisor k) := by
  rcases hready with ⟨hpc, h1, hn, hk', hdiv, _⟩
  have hnot : ¬ n ≤ k := by omega
  simp [execute, program, Machine.next, hpc, h1, hn, hk', hdiv, hnot,
    outputAdvanced, RAMState.setIndex, RAMState.setWord]

theorem outputAdvanced_ready (s : RAMState) (v : ℕ → ℚ) (divisor : ℚ) (n k : ℕ)
    (hready : OutputReady s v divisor n k) :
    OutputReady (outputAdvanced s v divisor k) v divisor n (k + 1) := by
  rcases hready with ⟨_, h1, hn, _, hdiv, hout⟩
  simp [OutputReady, outputAdvanced, outputPrefix, RAMState.setIndex, RAMState.setWord,
    h1, hn, hdiv, hout]

theorem output_loop (v : ℕ → ℚ) (B divisor : ℚ) (n p remaining k : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : OutputReady s v divisor n k) (hcount : k + remaining = n) :
    ∃ final : RAMState, Steps (program.next (input v B n p) tape) (7 * remaining) s final ∧
      OutputReady final v divisor n n := by
  induction remaining generalizing k s with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, hready⟩
  | succ remaining ih =>
    have hk : k < n := by omega
    have hsteps := execute_sound _ (output_cycle v B divisor n p k tape s hready hk)
    obtain ⟨final, hrun, hready'⟩ := ih (k + 1) (outputAdvanced s v divisor k)
      (outputAdvanced_ready s v divisor n k hready) (by omega)
    refine ⟨final, ?_, hready'⟩
    convert hsteps.trans hrun using 1
    omega

theorem finish (v : ℕ → ℚ) (B divisor : ℚ) (n p : ℕ) (tape : ℕ → Bool)
    (s : RAMState) (hready : OutputReady s v divisor n n) :
    Terminates (program.next (input v B n p) tape) 1 s {s with pc := 40} := by
  rcases hready with ⟨hpc, _, hn, hk, _, _⟩
  refine Terminates.step (t := {s with pc := 40}) ?_ ?_
  · simp [program, Machine.next, hpc, hn, hk]
  · exact Terminates.halt _ (by simp [program, Machine.next])

/-- Every execution is bounded by the proved linear transition count,
and returns exactly the vector divided by its dyadic upper norm estimate. -/
theorem terminates (v : ℕ → ℚ) (B : ℚ) (n p : ℕ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      Terminates (program.next (input v B n p) tape) (14 * n + 9 * p + 18)
        RAMState.initial final ∧ final.output = outputPrefix v (normUpper v B n p) n := by
  have hi := execute_sound _ (initialize_steps v B n p tape)
  obtain ⟨s₁, hs₁, hr₁⟩ := sum_loop v B n p n 0 tape (initialized B n p)
    (initialized_ready v B n p) (by omega)
  have hb := execute_sound _ (bisect_initialize_steps v B n p tape s₁ hr₁)
  obtain ⟨s₂, hs₂, hr₂⟩ := bisect_loop v B n p p 0 tape (bisectInitialized s₁ v B n)
    (bisectInitialized_ready s₁ v B n p hr₁) (by omega)
  have ho := execute_sound _ (output_initialize_steps v B n p tape s₂ hr₂)
  obtain ⟨s₃, hs₃, hr₃⟩ := output_loop v B (normUpper v B n p) n p n 0 tape
    (outputInitialized s₂ (normUpper v B n p)) (outputInitialized_ready s₂ v B n p hr₂) (by omega)
  refine ⟨{s₃ with pc := 40}, ?_, hr₃.2.2.2.2.2⟩
  have hsteps := ((((hi.trans hs₁).trans hb).trans hs₂).trans ho).trans hs₃
  have ht := hsteps.terminates (finish v B (normUpper v B n p) n p tape s₃ hr₃)
  convert ht using 1
  omega

def coordinates {n : ℕ} (v : Fin n → ℚ) (j : ℕ) : ℚ :=
  if h : j < n then v ⟨j, h⟩ else 0

@[simp] theorem coordinates_apply {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    coordinates v i.val = v i := by simp [coordinates]

theorem sumSquare_coordinates {n : ℕ} (v : Fin n → ℚ) :
    sumSquare (coordinates v) n = rationalNormSq v := by
  rw [sumSquare, ← Fin.sum_univ_eq_sum_range]
  simp [rationalNormSq]

theorem normUpper_coordinates {n : ℕ} (v : Fin n → ℚ) (B : ℚ) (p : ℕ) :
    normUpper (coordinates v) B n p = denominator v B p := by
  simp only [normUpper, scaledSquare, sumSquare_coordinates, denominator]

theorem outputPrefix_reverse (v : ℕ → ℚ) (divisor : ℚ) (n : ℕ) :
    outputPrefix v divisor n =
      ((List.range n).map (fun j => ((v j / divisor : ℚ) : ℝ))).reverse := by
  induction n with
  | zero => rfl
  | succ n ih => simp [outputPrefix, List.range_succ, ih]

theorem outputPrefix_vector {n : ℕ} (v : Fin n → ℚ) (B : ℚ) (p : ℕ) :
    outputPrefix (coordinates v) (denominator v B p) n =
      (List.ofFn (fun i : Fin n => ((vector v B p i : ℚ) : ℝ))).reverse := by
  rw [outputPrefix_reverse]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j < n := by simpa using hj
    simp [coordinates, hjn, vector, div_eq_mul_inv, mul_comm]

/-- The machine's actual output is the proved rational normalized vector,
with its norm and direction error, in the RAM's reverse output order. -/
theorem finite_vector_terminates {n : ℕ} (v : Fin n → ℚ) (B b : ℚ) (p : ℕ)
    (hB : 0 < B) (hb : 0 < b)
    (hlower : (b : ℝ) ≤ ‖rationalVector v‖) (hupper : ‖rationalVector v‖ ≤ (B : ℝ))
    (tape : ℕ → Bool) :
    ∃ final : RAMState,
      Terminates (program.next (input (coordinates v) B n p) tape) (14 * n + 9 * p + 18)
        RAMState.initial final ∧
      final.output = (List.ofFn (fun i : Fin n => ((vector v B p i : ℚ) : ℝ))).reverse ∧
      ‖rationalVector (vector v B p)‖ ≤ 1 ∧
      ‖rationalVector (vector v B p) - NormedSpace.normalize (rationalVector v)‖ ≤
        ((B / b : ℚ) : ℝ) * ((2 : ℝ) ^ p)⁻¹ := by
  obtain ⟨final, hrun, hout⟩ := terminates (coordinates v) B n p tape
  rw [normUpper_coordinates, outputPrefix_vector] at hout
  exact ⟨final, hrun, hout, vector_spec v B b p hB hb hlower hupper⟩

end Maxwell.Defect.RationalNormalize.RAM
