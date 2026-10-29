import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Dyadic density, finite strict-margin certificates, and fair search.

These are constructive search-control results. They do not replace the
construction of spectral enclosures from the finite Laurent operator.
-/

namespace Maxwell.Defect

theorem exists_dyadic_between {a b : ℝ} (hab : a < b) :
    ∃ (n : ℕ) (m : ℤ), a < (m : ℝ) / 2 ^ n ∧ (m : ℝ) / 2 ^ n < b := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hab)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hn' : 1 < (b - a) * (2 : ℝ) ^ n := by
    rw [div_pow, one_pow] at hn
    exact (div_lt_iff₀ hp).mp hn
  refine ⟨n, ⌊a * (2 : ℝ) ^ n⌋ + 1, ?_, ?_⟩
  · apply (lt_div_iff₀ hp).mpr
    simpa only [Int.cast_add, Int.cast_one] using Int.lt_floor_add_one (a * (2 : ℝ) ^ n)
  · apply (div_lt_iff₀ hp).mpr
    have hf := Int.floor_le (a * (2 : ℝ) ^ n)
    push_cast
    nlinarith

/-- Dyadic operating shifts approach the edge from below even when the
edge itself is irrational. -/
theorem exists_positive_dyadic_below {edge ε : ℝ} (he : 0 < edge) (hε : 0 < ε) :
    ∃ (n : ℕ) (m : ℤ),
      0 < (m : ℝ) / 2 ^ n ∧ (m : ℝ) / 2 ^ n < edge ∧
        0 < edge - (m : ℝ) / 2 ^ n ∧ edge - (m : ℝ) / 2 ^ n < ε := by
  have hmax : max 0 (edge - ε) < edge := max_lt he (by linarith)
  obtain ⟨n, m, hlo, hhi⟩ := exists_dyadic_between hmax
  refine ⟨n, m, lt_of_le_of_lt (le_max_left _ _) hlo, hhi, sub_pos.mpr hhi, ?_⟩
  have := lt_of_le_of_lt (le_max_right 0 (edge - ε)) hlo
  linarith

/-- The operating-shift enumeration uses exact rational arithmetic. -/
def dyadicCandidate (index : ℕ) : ℚ :=
  ((Nat.unpair index).1 : ℚ) / 2 ^ (Nat.unpair index).2

theorem exists_positive_dyadic_candidate {edge ε : ℝ} (he : 0 < edge) (hε : 0 < ε) :
    ∃ index, 0 < (dyadicCandidate index : ℝ) ∧
      (dyadicCandidate index : ℝ) < edge ∧ edge - (dyadicCandidate index : ℝ) < ε := by
  obtain ⟨n, m, hz, hze, _, hclose⟩ := exists_positive_dyadic_below he hε
  have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hm : 0 ≤ m := by
    have hmreal : 0 ≤ (m : ℝ) := ((div_pos_iff_of_pos_right hp).mp hz).le
    exact_mod_cast hmreal
  have heq : (dyadicCandidate (Nat.pair m.toNat n) : ℝ) = (m : ℝ) / 2 ^ n := by
    simp only [dyadicCandidate, Nat.unpair_pair, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hm
  exact ⟨Nat.pair m.toNat n, heq ▸ hz, heq ▸ hze, heq ▸ hclose⟩

/-- A decidable predicate containing only finitely many rational tests. -/
def marginCheck {k : ℕ} (approx : ℕ → Fin k → ℚ) (n : ℕ) : Prop :=
  ∀ i, (1 : ℚ) / 2 ^ n < approx n i

instance {k : ℕ} (approx : ℕ → Fin k → ℚ) : DecidablePred (marginCheck approx) :=
  fun n => inferInstanceAs (Decidable (∀ i, (1 : ℚ) / 2 ^ n < approx n i))

theorem marginCheck_sound {k : ℕ} (margin : Fin k → ℝ)
    (approx : ℕ → Fin k → ℚ) (n : ℕ)
    (herror : ∀ i, |(approx n i : ℝ) - margin i| ≤ (1 : ℝ) / 2 ^ n)
    (hcheck : marginCheck approx n) : ∀ i, 0 < margin i := by
  intro i
  have hcert : (1 : ℝ) / 2 ^ n < (approx n i : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr (hcheck i)
  have hi := (abs_le.mp (herror i)).2
  linarith

/-- A uniform positive margin has a finite rational acceptance precision. -/
theorem marginCheck_complete {k : ℕ} (margin : Fin k → ℝ)
    (approx : ℕ → Fin k → ℚ) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ i, δ ≤ margin i)
    (herror : ∀ n i, |(approx n i : ℝ) - margin i| ≤ (1 : ℝ) / 2 ^ n) :
    ∃ n, marginCheck approx n := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hδ)
    (by norm_num : (1 / 2 : ℝ) < 1)
  rw [div_pow, one_pow] at hn
  refine ⟨n, fun i => ?_⟩
  have hi := (abs_le.mp (herror n i)).1
  have hm := hmargin i
  have hcert : (1 : ℝ) / 2 ^ n < (approx n i : ℝ) := by linarith
  apply (Rat.cast_lt (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hcert

/-- Pair enumeration visits every candidate/precision pair in finite time. -/
theorem fair_search_has_success (check : ℕ → ℕ → Bool)
    (h : ∃ candidate precision, check candidate precision = true) :
    ∃ stage, check (Nat.unpair stage).1 (Nat.unpair stage).2 = true := by
  obtain ⟨candidate, precision, hcheck⟩ := h
  exact ⟨Nat.pair candidate precision, by simpa using hcheck⟩

/-- An executable least-stage search; existence enters only its termination
proof, and the runtime tests are the supplied finite Boolean checker. -/
def fixedSearch (check : ℕ → ℕ → Bool)
    (h : ∃ candidate precision, check candidate precision = true) : ℕ :=
  Nat.find (fair_search_has_success check h)

theorem fixedSearch_accepts (check : ℕ → ℕ → Bool)
    (h : ∃ candidate precision, check candidate precision = true) :
    check (Nat.unpair (fixedSearch check h)).1 (Nat.unpair (fixedSearch check h)).2 = true :=
  Nat.find_spec (fair_search_has_success check h)

theorem fixedSearch_le_success (check : ℕ → ℕ → Bool)
    (h : ∃ candidate precision, check candidate precision = true)
    (candidate precision : ℕ) (hpass : check candidate precision = true) :
    fixedSearch check h ≤ Nat.pair candidate precision := by
  apply Nat.find_min'
  simpa using hpass

end Maxwell.Defect
