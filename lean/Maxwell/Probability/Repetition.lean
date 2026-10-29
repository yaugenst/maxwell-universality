import Maxwell.Probability
import Mathlib.Data.Fintype.BigOperators

/-! Capped, verifiably accepted finite randomized trials and independent
repetition. The product sample space carries its actual uniform PMF. -/

namespace Maxwell.Probability
noncomputable section
open scoped Classical

variable {Ω Y : Type*} [Fintype Ω] [Nonempty Ω]

/-- Probability in the uniform finite experiment. -/
def uniformProbability (event : Finset Ω) : ℝ :=
  ((PMF.uniformOfFintype Ω).toOuterMeasure (event : Set Ω)).toReal

theorem uniformProbability_eq (event : Finset Ω) :
    uniformProbability event = (event.card : ℝ) / Fintype.card Ω := by
  unfold uniformProbability PMF.uniformOfFintype
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp

/-- The product space `Fin attempts → Ω` is the space of independent draws. -/
def allFailures (bad : Finset Ω) (attempts : ℕ) : Finset (Fin attempts → Ω) :=
  Fintype.piFinset fun _ => bad

omit [Fintype Ω] [Nonempty Ω] in
@[simp] theorem mem_allFailures (bad : Finset Ω) (attempts : ℕ)
    (draws : Fin attempts → Ω) :
    draws ∈ allFailures bad attempts ↔ ∀ i, draws i ∈ bad := by
  simp [allFailures]

/-- Exact independent repetition law, proved from the cardinality of the
product finite event rather than an independence premise. -/
theorem independent_failure_probability (bad : Finset Ω) (attempts : ℕ) :
    uniformProbability (allFailures bad attempts) =
      (uniformProbability bad)^attempts := by
  rw [uniformProbability_eq, uniformProbability_eq]
  simp [allFailures, div_pow]

/-- A cap is passed to each run. The interface's `used ≤ cap` invariant is
the exact operational resource promise required of the timeout wrapper. -/
structure CappedResult (Y : Type*) (cap : ℕ) where
  used : ℕ
  used_le_cap : used ≤ cap
  output : Option Y

/-- A returned value is accepted only after the supplied decidable check. -/
def verifiedOutput (verify : Y → Bool) {cap : ℕ} (result : CappedResult Y cap) : Option Y :=
  result.output.filter verify

theorem verifiedOutput_sound (verify : Y → Bool) (correct : Y → Prop)
    (hsound : ∀ y, verify y = true → correct y) {cap : ℕ} (result : CappedResult Y cap)
    {y : Y} (hy : verifiedOutput verify result = some y) : correct y := by
  cases hout : result.output with
  | none => simp [verifiedOutput, hout] at hy
  | some z =>
    simp [verifiedOutput, hout] at hy
    exact hsound y hy.2

/-- Returning the first accepted trial does not require any promise about
which physical draw produced that value. -/
def firstSome : List (Option Y) → Option Y
  | [] => none
  | none :: rest => firstSome rest
  | some y :: _ => some y

theorem firstSome_eq_none (xs : List (Option Y)) :
    firstSome xs = none ↔ ∀ x ∈ xs, x = none := by
  induction xs with
  | nil => simp [firstSome]
  | cons x xs ih =>
    cases x <;> simp [firstSome, ih]

theorem firstSome_mem {xs : List (Option Y)} {y : Y}
    (h : firstSome xs = some y) : some y ∈ xs := by
  induction xs with
  | nil => simp [firstSome] at h
  | cons x xs ih =>
    cases x with
    | none => exact List.mem_cons_of_mem _ (ih h)
    | some z => simp_all [firstSome]

/-- Prescribed capped attempts and exact verification; the recursion simply
returns the first verified output. -/
def repeatCapped (cap attempts : ℕ) (run : Ω → CappedResult Y cap)
    (verify : Y → Bool) (draws : Fin attempts → Ω) : Option Y :=
  firstSome (List.ofFn fun i => verifiedOutput verify (run (draws i)))

def failedTrial (cap : ℕ) (run : Ω → CappedResult Y cap)
    (verify : Y → Bool) : Finset Ω :=
  Finset.univ.filter fun ω => verifiedOutput verify (run ω) = none

omit [Fintype Ω] [Nonempty Ω] in
theorem repeatCapped_sound (cap attempts : ℕ) (run : Ω → CappedResult Y cap)
    (verify : Y → Bool) (correct : Y → Prop)
    (hsound : ∀ y, verify y = true → correct y)
    (draws : Fin attempts → Ω) {y : Y}
    (hy : repeatCapped cap attempts run verify draws = some y) : correct y := by
  have hmem := firstSome_mem hy
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  exact verifiedOutput_sound verify correct hsound (run (draws i)) hi

omit [Nonempty Ω] in
theorem repeatCapped_failure_iff (cap attempts : ℕ) (run : Ω → CappedResult Y cap)
    (verify : Y → Bool) (draws : Fin attempts → Ω) :
    repeatCapped cap attempts run verify draws = none ↔
      draws ∈ allFailures (failedTrial cap run verify) attempts := by
  simp [repeatCapped, firstSome_eq_none, failedTrial, List.mem_ofFn]

omit [Fintype Ω] [Nonempty Ω] in
/-- Cost is bounded on every sample tuple, including all failed and timeout
draws. Add deterministic encoding/verification cost into `overhead`. -/
theorem repeatCapped_all_draw_cost (cap attempts overhead : ℕ)
    (run : Ω → CappedResult Y cap) (draws : Fin attempts → Ω) :
    (∑ i, ((run (draws i)).used + overhead)) ≤ attempts * (cap + overhead) := by
  calc
    _ ≤ ∑ _ : Fin attempts, (cap + overhead) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.add_le_add_right (run (draws i)).used_le_cap overhead
    _ = _ := by simp

/-- The failure probability of the implemented verified repetition is
exactly the power of its one-trial failure probability. -/
theorem repeatCapped_failure_probability (cap attempts : ℕ)
    (run : Ω → CappedResult Y cap) (verify : Y → Bool) :
    uniformProbability (Finset.univ.filter fun draws : Fin attempts → Ω =>
      repeatCapped cap attempts run verify draws = none) =
        (uniformProbability (failedTrial cap run verify))^attempts := by
  have hevent : (Finset.univ.filter fun draws : Fin attempts → Ω =>
      repeatCapped cap attempts run verify draws = none) =
        allFailures (failedTrial cap run verify) attempts := by
    ext draws
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact repeatCapped_failure_iff cap attempts run verify draws
  rw [hevent, independent_failure_probability]

/-- A logarithmic number of independent trials turns any one-trial failure
bound of one half into any prescribed inverse polynomial. -/
theorem amplification_inverse_polynomial (bad : Finset Ω) (m q : ℕ)
    (hm : 0 < m) (hfail : uniformProbability bad ≤ 1 / 2) :
    uniformProbability (allFailures bad (q * Nat.clog 2 m)) ≤ 1 / (m : ℝ)^q := by
  rw [independent_failure_probability]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    (uniformProbability bad)^(q * Nat.clog 2 m) ≤ (1 / 2 : ℝ)^(q * Nat.clog 2 m) :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hfail _
    _ = 1 / ((2 : ℝ)^Nat.clog 2 m)^q := by
      rw [Nat.mul_comm q, pow_mul]
      simp only [one_div_pow]
    _ ≤ 1 / (m : ℝ)^q := by
      apply one_div_le_one_div_of_le (by positivity)
      apply pow_le_pow_left₀ hmR.le
      exact_mod_cast Nat.le_pow_clog (b := 2) (by norm_num) m

/-- A fixed positive one-trial success probability suffices: a constant
block size, independent of input size and requested exponent, gives the
same logarithmic repetition count. -/
theorem fixed_success_amplification (bad : Finset Ω)
    (hfail : uniformProbability bad < 1) :
    ∃ block : ℕ, 0 < block ∧ ∀ m q : ℕ, 0 < m →
      uniformProbability (allFailures bad (block * (q * Nat.clog 2 m))) ≤
        1 / (m : ℝ)^q := by
  obtain ⟨block, hblock⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hfail
  have hbpos : 0 < block := by
    by_contra h
    have hbzero : block = 0 := by omega
    norm_num [hbzero] at hblock
  refine ⟨block, hbpos, ?_⟩
  intro m q hm
  have hhalf : uniformProbability (allFailures bad block) ≤ 1 / 2 := by
    rw [independent_failure_probability]
    exact hblock.le
  have h := amplification_inverse_polynomial (allFailures bad block) m q hm hhalf
  simpa only [independent_failure_probability, pow_mul] using h

/-- A genuine timeout wrapper for a step-by-step solver. It performs at
most `cap` transition steps and returns `none` if no halt was seen. -/
def runWithCap {S : Type*} (step : S → S) (halt : S → Option Y) :
    (cap : ℕ) → S → CappedResult Y cap
  | 0, state => ⟨0, le_rfl, halt state⟩
  | cap + 1, state =>
    match halt state with
    | some y => ⟨0, Nat.zero_le _, some y⟩
    | none =>
      let result := runWithCap step halt cap (step state)
      ⟨result.used + 1, Nat.add_le_add_right result.used_le_cap 1, result.output⟩

/-- The timeout wrapper really enforces the cap on every state. -/
theorem runWithCap_steps {S : Type*} (step : S → S) (halt : S → Option Y)
    (cap : ℕ) (state : S) : (runWithCap step halt cap state).used ≤ cap :=
  (runWithCap step halt cap state).used_le_cap

/-- A solver which reaches an accepted halt within the cap cannot be lost
to timeout; no condition is imposed on states beyond that cap. -/
theorem runWithCap_complete {S : Type*} (step : S → S) (halt : S → Option Y)
    (cap : ℕ) (state : S) (verify : Y → Bool)
    (hwithin : ∃ t ≤ cap, ∃ y, halt (step^[t] state) = some y ∧ verify y = true)
    (haccepted : ∀ t ≤ cap, ∀ y, halt (step^[t] state) = some y → verify y = true) :
    ∃ y, (runWithCap step halt cap state).output = some y ∧ verify y = true := by
  induction cap generalizing state with
  | zero =>
    obtain ⟨t, ht, y, hy, hv⟩ := hwithin
    have ht0 : t = 0 := by omega
    subst t
    exact ⟨y, by simpa [runWithCap] using hy, hv⟩
  | succ cap ih =>
    cases hh : halt state with
    | some y =>
      refine ⟨y, by simp [runWithCap, hh], ?_⟩
      exact haccepted 0 (Nat.zero_le _) y (by simpa using hh)
    | none =>
      obtain ⟨t, ht, y, hy, hv⟩ := hwithin
      have htpos : 0 < t := by
        by_contra hn
        have htzero : t = 0 := by omega
        subst t
        simp [hh] at hy
      obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
      have hnext : ∃ t ≤ cap, ∃ y,
          halt (step^[t] (step state)) = some y ∧ verify y = true := by
        refine ⟨t', by omega, y, ?_, hv⟩
        simpa only [Function.iterate_succ_apply] using hy
      have hnextAccepted : ∀ t ≤ cap, ∀ y,
          halt (step^[t] (step state)) = some y → verify y = true := by
        intro t ht y hy
        apply haccepted (t + 1) (by omega) y
        simpa only [Function.iterate_succ_apply] using hy
      obtain ⟨z, hz, hvz⟩ := ih (step state) hnext hnextAccepted
      exact ⟨z, by simpa [runWithCap, hh] using hz, hvz⟩

end
end Maxwell.Probability
