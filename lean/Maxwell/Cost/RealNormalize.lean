import Maxwell.Cost.RealSparse

/-! Exact normalization of unrestricted real words by a fixed finite
Real-RAM program. The maximum absolute value and the real-valued count
are computed by the scan; no floor, real-to-index cast, or host maximum
is available as an instruction. -/

namespace Maxwell.Cost.RealNormalize

open RealSparse (execute execute_sound execute_add)

set_option maxRecDepth 20000

noncomputable def input (n : ℕ) (v : ℕ → ℝ) : RAMInput :=
  ⟨v, fun a => if a = 0 then n else 0⟩

noncomputable def maxAbs (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => max (maxAbs v k) |v k|

/-- `byCount` selects matrix normalization `v/(n max|v|)` or source
normalization `v/max|v|`. It is a fixed code choice, independent of input. -/
def program (byCount : Bool) : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .inputIndex 2 0,
  .indexLiteral 3 0, .literal 0 0, .literal 1 0,
  .literal 2 0, .literal 3 (-1), .literal 4 1,
  .branchIndexLE 2 3 25 10,
  .input 5 3, .multiply 6 3 5, .branchLE 5 6 13 15,
  .copy 5 6, .jump 17, .copy 5 5, .jump 17,
  .branchLE 0 5 18 20, .copy 0 5, .jump 22, .copy 0 0, .jump 22,
  .add 1 1 4, .indexAdd 3 3 1, .jump 9,
  (if byCount then .multiply 7 0 1 else .copy 7 0), .indexLiteral 3 0,
  .branchIndexLE 2 3 37 28,
  .input 5 3, .branchLE 0 2 30 32,
  .literal 5 0, .jump 34, .divide 5 5 7, .jump 34,
  .output 5, .indexAdd 3 3 1, .jump 27, .halt]⟩

def MaxReady (s : RAMState) (v : ℕ → ℝ) (n k : ℕ) : Prop :=
  s.pc = 9 ∧ s.indices 1 = 1 ∧ s.indices 2 = n ∧ s.indices 3 = k ∧
    s.words 0 = maxAbs v k ∧ s.words 1 = k ∧ s.words 2 = 0 ∧
    s.words 3 = -1 ∧ s.words 4 = 1 ∧ s.output = [] ∧ s.indexOutput = [] ∧ s.randomCursor = 0

noncomputable def initialized (n : ℕ) : RAMState :=
  let s := RAMState.initial.setIndex 0 0
  let s := s.setIndex 1 1
  let s := s.setIndex 2 n
  let s := s.setIndex 3 0
  let s := s.setWord 0 0
  let s := s.setWord 1 0
  let s := s.setWord 2 0
  let s := s.setWord 3 (-1)
  s.setWord 4 1

theorem initialize_steps (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (tape : ℕ → Bool) :
    execute ((program byCount).next (input n v) tape) 9 RAMState.initial = some (initialized n) := by
  simp [execute, program, Machine.next, initialized, input, RAMState.initial, RAMState.setIndex, RAMState.setWord]

theorem initialized_ready (n : ℕ) (v : ℕ → ℝ) : MaxReady (initialized n) v n 0 := by
  simp [MaxReady, initialized, maxAbs, RAMState.initial, RAMState.setIndex, RAMState.setWord]

noncomputable def maxMiddle (s : RAMState) (x : ℝ) : RAMState :=
  let t := {s with pc := 10}
  let t := t.setWord 5 x
  let t := t.setWord 6 (-x)
  let t := t.setWord 5 |x|
  {t with pc := 17}

noncomputable def maxAdvanced (s : RAMState) (x : ℝ) : RAMState :=
  let t := maxMiddle s x
  let t := t.setWord 0 (max (s.words 0) |x|)
  let t := t.setWord 1 (s.words 1 + 1)
  let t := t.setIndex 3 (s.indices 3 + 1)
  {t with pc := 9}

set_option maxHeartbeats 1200000 in
theorem max_cycle (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (tape : ℕ → Bool)
    (s : RAMState) (k : ℕ) (h : MaxReady s v n k) (hk : k < n) :
    execute ((program byCount).next (input n v) tape) 12 s = some (maxAdvanced s (v k)) := by
  rcases h with ⟨hpc, h1, hn, hi, _, _, _, hm, hw, _, _, _⟩
  have hnot : ¬ n ≤ k := by omega
  have hfirst : execute ((program byCount).next (input n v) tape) 6 s = some (maxMiddle s (v k)) := by
    by_cases hx : v k ≤ -v k
    · have hneg : v k ≤ 0 := by linarith
      simp [execute, program, Machine.next, hpc, hn, hi, hm, hnot, hx,
        input, maxMiddle, RAMState.setWord, abs_of_nonpos hneg]
    · have hpos : 0 ≤ v k := by linarith
      simp [execute, program, Machine.next, hpc, hn, hi, hm, hnot, hx,
        input, maxMiddle, RAMState.setWord, abs_of_nonneg hpos]
  rw [show 12 = 6 + 6 from rfl, execute_add, hfirst, Option.bind_some]
  by_cases hx : s.words 0 ≤ |v k|
  · simp [execute, program, Machine.next, h1, hi, hw, hx, maxMiddle, maxAdvanced,
      RAMState.setWord, RAMState.setIndex]
  · simp [execute, program, Machine.next, h1, hi, hw, hx, maxMiddle, maxAdvanced,
      RAMState.setWord, RAMState.setIndex, max_eq_left (le_of_not_ge hx)]

theorem maxAdvanced_ready (s : RAMState) (v : ℕ → ℝ) (n k : ℕ) (h : MaxReady s v n k) :
    MaxReady (maxAdvanced s (v k)) v n (k + 1) := by
  rcases h with ⟨_, h1, hn, hi, hmax, hcount, hz, hm, hw, ho, hio, hr⟩
  simp [MaxReady, maxAdvanced, maxMiddle, maxAbs, RAMState.setWord, RAMState.setIndex,
    h1, hn, hi, hmax, hcount, hz, hm, hw, ho, hio, hr]

theorem max_scan (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (tape : ℕ → Bool)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (h : MaxReady s v n k) (hcount : k + remaining = n) :
    ∃ final : RAMState,
      Steps ((program byCount).next (input n v) tape) (12 * remaining) s final ∧ MaxReady final v n n := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, h⟩
  | succ remaining ih =>
    have hk : k < n := by omega
    obtain ⟨f, hf, hfr⟩ := ih (maxAdvanced s (v k)) (k + 1) (maxAdvanced_ready s v n k h) (by omega)
    refine ⟨f, ?_, hfr⟩
    convert (execute_sound _ (max_cycle byCount n v tape s k h hk)).trans hf using 1
    omega

noncomputable def scale (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) : ℝ :=
  if byCount then maxAbs v n * n else maxAbs v n

noncomputable def normalized (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (j : ℕ) : ℝ :=
  if maxAbs v n ≤ 0 then 0 else v j / scale byCount n v

def OutputReady (s : RAMState) (byCount : Bool) (v : ℕ → ℝ) (n k : ℕ) : Prop :=
  s.pc = 27 ∧ s.indices 1 = 1 ∧ s.indices 2 = n ∧ s.indices 3 = k ∧
    s.words 0 = maxAbs v n ∧ s.words 2 = 0 ∧ s.words 7 = scale byCount n v ∧
    s.indexOutput = [] ∧ s.randomCursor = 0

noncomputable def outputInitialized (s : RAMState) (byCount : Bool) : RAMState :=
  let t := ({s with pc := 25}).setWord 7 (if byCount then s.words 0 * s.words 1 else s.words 0)
  t.setIndex 3 0

theorem output_initialize (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (tape : ℕ → Bool)
    (s : RAMState) (h : MaxReady s v n n) :
    execute ((program byCount).next (input n v) tape) 3 s = some (outputInitialized s byCount) := by
  rcases h with ⟨hpc, _, hn, hi, _, _, _, _, _, _, _, _⟩
  cases byCount <;> simp [execute, program, Machine.next, hpc, hn, hi,
    outputInitialized, RAMState.setWord, RAMState.setIndex]

theorem outputInitialized_ready (s : RAMState) (byCount : Bool) (v : ℕ → ℝ) (n : ℕ)
    (h : MaxReady s v n n) : OutputReady (outputInitialized s byCount) byCount v n 0 := by
  rcases h with ⟨_, h1, hn, _, hm, hc, hz, _, _, _, hio, hr⟩
  simp [OutputReady, outputInitialized, scale, RAMState.setWord, RAMState.setIndex,
    h1, hn, hm, hc, hz, hio, hr]

noncomputable def outputAdvanced (s : RAMState) (x : ℝ) : RAMState :=
  let value := if s.words 0 ≤ s.words 2 then 0 else x / s.words 7
  let t := s.setWord 5 value
  let t := t.setIndex 3 (s.indices 3 + 1)
  {t with pc := 27, output := value :: s.output}

set_option maxHeartbeats 1000000 in
theorem output_cycle (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (tape : ℕ → Bool)
    (s : RAMState) (k : ℕ) (h : OutputReady s byCount v n k) (hk : k < n) :
    execute ((program byCount).next (input n v) tape) 8 s = some (outputAdvanced s (v k)) := by
  rcases h with ⟨hpc, h1, hn, hi, _, _, _, _, _⟩
  have hnot : ¬ n ≤ k := by omega
  by_cases hz : s.words 0 ≤ s.words 2
  · simp [execute, program, Machine.next, input, hpc, h1, hn, hi, hnot, hz,
      outputAdvanced, RAMState.setWord, RAMState.setIndex]
  · simp [execute, program, Machine.next, input, hpc, h1, hn, hi, hnot, hz,
      outputAdvanced, RAMState.setWord, RAMState.setIndex]

theorem outputAdvanced_ready (s : RAMState) (byCount : Bool) (v : ℕ → ℝ) (n k : ℕ)
    (h : OutputReady s byCount v n k) (x : ℝ) :
    OutputReady (outputAdvanced s x) byCount v n (k + 1) := by
  rcases h with ⟨_, h1, hn, hi, hm, hz, hd, hio, hr⟩
  simp [OutputReady, outputAdvanced, RAMState.setWord, RAMState.setIndex, h1, hn, hi, hm, hz, hd, hio, hr]

noncomputable def outputWords (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (start : ℕ) : ℕ → List ℝ
  | 0 => []
  | k + 1 => normalized byCount n v start :: outputWords byCount n v (start + 1) k

theorem output_scan (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (tape : ℕ → Bool)
    (remaining : ℕ) (s : RAMState) (k : ℕ) (h : OutputReady s byCount v n k) (hcount : k + remaining = n) :
    ∃ final : RAMState,
      Steps ((program byCount).next (input n v) tape) (8 * remaining) s final ∧
      OutputReady final byCount v n n ∧
      final.output = (outputWords byCount n v k remaining).reverse ++ s.output := by
  induction remaining generalizing s k with
  | zero =>
    have hk : k = n := by omega
    subst k
    exact ⟨s, Steps.refl s, h, rfl⟩
  | succ remaining ih =>
    have hk : k < n := by omega
    obtain ⟨f, hf, hfr, hfo⟩ := ih (outputAdvanced s (v k)) (k + 1)
      (outputAdvanced_ready s byCount v n k h _) (by omega)
    refine ⟨f, ?_, hfr, ?_⟩
    · convert (execute_sound _ (output_cycle byCount n v tape s k h hk)).trans hf using 1
      omega
    · simpa [outputWords, outputAdvanced, normalized, h.2.2.2.2.1, h.2.2.2.2.2.1,
        h.2.2.2.2.2.2.1, List.append_assoc] using hfo

theorem terminates (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      Terminates ((program byCount).next (input n v) tape) (20 * n + 13) RAMState.initial final ∧
      final.output.reverse = outputWords byCount n v 0 n ∧
      final.words 0 = maxAbs v n ∧ final.words 7 = scale byCount n v ∧
      final.indexOutput = [] ∧ final.randomCursor = 0 := by
  have hi := execute_sound _ (initialize_steps byCount n v tape)
  obtain ⟨a, ha, har⟩ := max_scan byCount n v tape n (initialized n) 0 (initialized_ready n v) (by omega)
  have ho := execute_sound _ (output_initialize byCount n v tape a har)
  obtain ⟨b, hb, hbr, hbo⟩ := output_scan byCount n v tape n
    (outputInitialized a byCount) 0 (outputInitialized_ready a byCount v n har) (by omega)
  have he : Terminates ((program byCount).next (input n v) tape) 1 b {b with pc := 37} := by
    apply Terminates.step (t := {b with pc := 37})
    · simp [program, Machine.next, hbr.1, hbr.2.2.1, hbr.2.2.2.1]
    · exact Terminates.halt _ (by simp [program, Machine.next])
  refine ⟨{b with pc := 37}, ?_, ?_, hbr.2.2.2.2.1, hbr.2.2.2.2.2.2.1,
    hbr.2.2.2.2.2.2.2.1, hbr.2.2.2.2.2.2.2.2⟩
  · convert (((hi.trans ha).trans ho).trans hb).terminates he using 1
    omega
  · change b.output.reverse = _
    rw [hbo]
    change (_ ++ a.output).reverse = _
    rw [har.2.2.2.2.2.2.2.2.2.1]
    simp

theorem run (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (tape : ℕ → Bool) :
    ∃ final : RAMState,
      ((program byCount).run (input n v) tape (20 * n + 14)).finished = some final ∧
      ((program byCount).run (input n v) tape (20 * n + 14)).instructions = 20 * n + 13 ∧
      final.output.reverse = outputWords byCount n v 0 n ∧
      final.words 0 = maxAbs v n ∧ final.words 7 = scale byCount n v := by
  obtain ⟨final, ht, ho, hm, hd, _, _⟩ := terminates byCount n v tape
  obtain ⟨hf, hc⟩ := runCapped_of_terminates _ ht
  exact ⟨final, hf, hc, ho, hm, hd⟩

theorem maxAbs_nonneg (v : ℕ → ℝ) (n : ℕ) : 0 ≤ maxAbs v n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem abs_le_maxAbs (v : ℕ → ℝ) (n k : ℕ) (hk : k < n) : |v k| ≤ maxAbs v n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst k
      exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

theorem maxAbs_eq_zero_iff (v : ℕ → ℝ) (n : ℕ) :
    maxAbs v n = 0 ↔ ∀ k < n, v k = 0 := by
  constructor
  · intro h k hk
    have hb := abs_le_maxAbs v n k hk
    rw [h] at hb
    exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
  · intro h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [maxAbs, ih (fun k hk => h k (by omega)), h n (by omega)]
      simp

theorem maxAbs_pos (v : ℕ → ℝ) (n : ℕ) (h : ∃ k < n, v k ≠ 0) : 0 < maxAbs v n := by
  obtain ⟨k, hk, hv⟩ := h
  exact (abs_pos.mpr hv).trans_le (abs_le_maxAbs v n k hk)

theorem maxAbs_attained (v : ℕ → ℝ) (n : ℕ) (h : 0 < maxAbs v n) :
    ∃ k < n, |v k| = maxAbs v n := by
  induction n with
  | zero => simp [maxAbs] at h
  | succ n ih =>
    by_cases hn : maxAbs v n ≤ |v n|
    · exact ⟨n, by omega, (max_eq_right hn).symm⟩
    · have hp : 0 < maxAbs v n := (abs_nonneg (v n)).trans_lt (lt_of_not_ge hn)
      obtain ⟨k, hk, he⟩ := ih hp
      exact ⟨k, by omega, he.trans (max_eq_left (le_of_not_ge hn)).symm⟩

theorem scale_pos (byCount : Bool) (n : ℕ) (v : ℕ → ℝ) (h : 0 < maxAbs v n) :
    0 < scale byCount n v := by
  have hn : 0 < n := by
    by_contra hn
    have hz : n = 0 := by omega
    simp [hz, maxAbs] at h
  cases byCount <;> simp [scale, h, hn]

/-- The all-zero test is exact even for arbitrarily small nonzero inputs. -/
theorem normalized_zero (byCount : Bool) (n : ℕ) (v : ℕ → ℝ)
    (h : maxAbs v n = 0) (k : ℕ) : normalized byCount n v k = 0 := by simp [normalized, h]

theorem normalized_source_abs_le (n : ℕ) (v : ℕ → ℝ) (k : ℕ) (hk : k < n) :
    |normalized false n v k| ≤ 1 := by
  by_cases h : maxAbs v n ≤ 0
  · simp [normalized, h]
  · have hp : 0 < maxAbs v n := lt_of_not_ge h
    simp only [normalized, h, scale, Bool.false_eq_true, ↓reduceIte, abs_div, abs_of_pos hp]
    exact (div_le_one hp).mpr (abs_le_maxAbs v n k hk)

/-- A nonzero source has an actually attained normalized unit coordinate. -/
theorem normalized_source_attained (n : ℕ) (v : ℕ → ℝ) (h : 0 < maxAbs v n) :
    ∃ k < n, |normalized false n v k| = 1 := by
  obtain ⟨k, hk, hv⟩ := maxAbs_attained v n h
  refine ⟨k, hk, ?_⟩
  simp [normalized, not_le_of_gt h, scale, abs_div, abs_of_pos h, hv, ne_of_gt h]

theorem normalized_matrix_abs_le (n : ℕ) (v : ℕ → ℝ) (k : ℕ) (hk : k < n) :
    |normalized true n v k| ≤ 1 / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  by_cases h : maxAbs v n ≤ 0
  · simp [normalized, h, le_of_lt hn]
  · have hp : 0 < maxAbs v n := lt_of_not_ge h
    have hd : 0 < maxAbs v n * (n : ℝ) := mul_pos hp hn
    simp only [normalized, h, ↓reduceIte, scale, abs_div, abs_of_pos hd]
    calc
      |v k| / (maxAbs v n * n) ≤ maxAbs v n / (maxAbs v n * n) :=
        div_le_div_of_nonneg_right (abs_le_maxAbs v n k hk) hd.le
      _ = 1 / (n : ℝ) := by field_simp

theorem normalized_matrix_sum_abs_le (n : ℕ) (v : ℕ → ℝ) :
    (∑ k ∈ Finset.range n, |normalized true n v k|) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · calc
      _ ≤ ∑ _ ∈ Finset.range n, (1 / (n : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact normalized_matrix_abs_le n v k (Finset.mem_range.mp hk)
      _ = 1 := by simp [hn]

end Maxwell.Cost.RealNormalize
