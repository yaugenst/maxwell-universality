import Maxwell.Continuum.DetuningGrid
import Mathlib.Data.Nat.Log

/-!
# Finite sampling for continuum scalar detuning

This file proves the finite-grid counting and probability part of the continuum
detuning lemma. Its input is a finite list of possible spectral obstructions,
bounded in cardinality by `N`. It does not assert that the spectrum of a
particular Maxwell operator has this form. The continuum operator construction
and its spectral count must supply that input separately.

The interval occupancy estimate is extracted from `Maxwell.Probability` into `DetuningGrid`, where it
is proved from the extreme indices of a finite subset of the midpoint lattice.
No discrete Maxwell certificate is imported or assumed.
-/

namespace Maxwell.Continuum.Detuning

noncomputable section

open scoped Classical

/-- The continuum inverse budget, with `N` the bound for the number of local
spectral obstructions. -/
def inverseBudget (m N : ℕ) (τ : ℝ) : ℝ := 64 * m * N / τ

/-- Distance excluded around each spectral obstruction. -/
def radius (m N : ℕ) (τ : ℝ) : ℝ := τ / (64 * m * N)

theorem radius_eq_inverseBudget_inv (m N : ℕ) (τ : ℝ) :
    radius m N τ = 1 / inverseBudget m N τ := by
  simp [radius, inverseBudget, div_eq_mul_inv]

theorem inverseBudget_pos (m N : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) :
    0 < inverseBudget m N τ := by
  dsimp [inverseBudget]
  positivity

theorem radius_pos (m N : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) :
    0 < radius m N τ := by
  dsimp [radius]
  positivity

theorem grid_pos (m N J : ℕ) (hm : 0 < m) (hN : 0 < N)
    (hgrid : 64 * m * N ≤ J) : 0 < J := by
  have h : 0 < 64 * m * N := by positivity
  exact h.trans_le hgrid

/-- Bad draws for an arbitrary finite set of real spectral values. Strict
inequality makes equality at the inverse-budget endpoint a good draw. -/
def badDraws (s : Finset ℝ) (τ r : ℝ) (J : ℕ) : Finset ℕ :=
  s.biUnion (fun eig => Maxwell.Continuum.DetuningGrid.nearGrid τ r eig J)

@[simp] theorem mem_badDraws (s : Finset ℝ) (τ r : ℝ) (J j : ℕ) :
    j ∈ badDraws s τ r J ↔
      j < J ∧ ∃ eig ∈ s, |eig - Maxwell.Continuum.DetuningGrid.midpoint τ J j| < r := by
  simp [badDraws, Maxwell.Continuum.DetuningGrid.nearGrid, and_left_comm, exists_and_left]

theorem badDraws_subset (s : Finset ℝ) (τ r : ℝ) (J : ℕ) :
    badDraws s τ r J ⊆ Finset.range J := by
  intro j hj
  exact Finset.mem_range.mpr ((mem_badDraws _ _ _ _ _).mp hj).1

/-- The actual union bound, using the proved midpoint-lattice occupancy
estimate for each individual interval. -/
theorem badDraws_card_le (s : Finset ℝ) (τ r : ℝ) (J : ℕ)
    (hτ : 0 < τ) (hr : 0 ≤ r) (hJ : 0 < J) :
    ((badDraws s τ r J).card : ℝ) ≤ s.card * (2 * r * J / τ + 1) := by
  calc
    ((badDraws s τ r J).card : ℝ) ≤
        ∑ eig ∈ s, ((Maxwell.Continuum.DetuningGrid.nearGrid τ r eig J).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := s)
        (t := fun eig => Maxwell.Continuum.DetuningGrid.nearGrid τ r eig J))
    _ ≤ ∑ _eig ∈ s, (2 * r * J / τ + 1) :=
      Finset.sum_le_sum (fun eig _ =>
        Maxwell.Continuum.DetuningGrid.nearGrid_card_le τ r eig J hτ hr hJ)
    _ = s.card * (2 * r * J / τ + 1) := by simp; ring

/-- Probability under the actual uniform distribution on the emitted indices. -/
theorem badDraws_probability_le (s : Finset ℝ) (τ r : ℝ) (J : ℕ)
    (hτ : 0 < τ) (hr : 0 ≤ r) (hJ : 0 < J) :
    Maxwell.Continuum.DetuningGrid.gridProbability J hJ (badDraws s τ r J) ≤
      2 * s.card * r / τ + s.card / J := by
  rw [Maxwell.Continuum.DetuningGrid.gridProbability_eq _ _ _ (badDraws_subset _ _ _ _)]
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  calc
    ((badDraws s τ r J).card : ℝ) / J ≤
        (s.card * (2 * r * J / τ + 1)) / J :=
      div_le_div_of_nonneg_right (badDraws_card_le s τ r J hτ hr hJ) hJR.le
    _ = 2 * s.card * r / τ + s.card / J := by field_simp

/-- The continuum constants give the exact failure probability `3 / (64 m)`.
The only spectral premise is the explicit cardinality bound on the supplied
finite set; individual interval counts and the uniform law are proved. -/
theorem finite_detuning_probability (s : Finset ℝ) (m N J : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ)
    (hcount : s.card ≤ N) (hgrid : 64 * m * N ≤ J) :
    Maxwell.Continuum.DetuningGrid.gridProbability J (grid_pos m N J hm hN hgrid)
      (badDraws s τ (radius m N τ) J) ≤ 3 / (64 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : (0 : ℝ) < 64 * m * N := by positivity
  have hcountR : (s.card : ℝ) ≤ N := by exact_mod_cast hcount
  have hgridR : 64 * (m : ℝ) * N ≤ J := by exact_mod_cast hgrid
  have hJ := grid_pos m N J hm hN hgrid
  have hr := radius_pos m N τ hm hN hτ
  have hraw := badDraws_probability_le s τ (radius m N τ) J hτ hr.le hJ
  have hfirst : 2 * (s.card : ℝ) * radius m N τ / τ ≤
      2 * N * radius m N τ / τ := by gcongr
  have hsecond : (s.card : ℝ) / J ≤ N / (64 * (m : ℝ) * N) := by
    calc
      (s.card : ℝ) / J ≤ N / J := by gcongr
      _ ≤ N / (64 * (m : ℝ) * N) :=
        div_le_div_of_nonneg_left hNR.le hden hgridR
  calc
    _ ≤ 2 * N * radius m N τ / τ + N / (64 * (m : ℝ) * N) := by linarith
    _ = 3 / (64 * (m : ℝ)) := by
      dsimp [radius]
      field_simp
      ring

/-- The cardinality fraction is the same quantity as the PMF probability. -/
theorem finite_detuning_fraction (s : Finset ℝ) (m N J : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ)
    (hcount : s.card ≤ N) (hgrid : 64 * m * N ≤ J) :
    ((badDraws s τ (radius m N τ) J).card : ℝ) / J ≤
      3 / (64 * (m : ℝ)) := by
  simpa only [Maxwell.Continuum.DetuningGrid.gridProbability_eq _ _ _
    (badDraws_subset _ _ _ _)] using
    finite_detuning_probability s m N J τ hm hN hτ hcount hgrid

/-- The exact number of independent fair bits required by the continuum grid. -/
def randomBits (m N : ℕ) : ℕ := Nat.clog 2 (64 * m * N)

/-- The least power of two no smaller than `64 m N`. -/
def gridSize (m N : ℕ) : ℕ := 2 ^ randomBits m N

theorem gridSize_sufficient (m N : ℕ) : 64 * m * N ≤ gridSize m N :=
  Nat.le_pow_clog (by norm_num) _

theorem gridSize_least (m N bits : ℕ) (h : 64 * m * N ≤ 2 ^ bits) :
    gridSize m N ≤ 2 ^ bits := by
  exact Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow h)

theorem randomBits_le (m N : ℕ) :
    randomBits m N ≤ 6 + Nat.clog 2 m + Nat.clog 2 N := by
  apply Nat.clog_le_of_le_pow
  have hm := Nat.le_pow_clog (b := 2) (by norm_num) m
  have hN := Nat.le_pow_clog (b := 2) (by norm_num) N
  calc
    64 * m * N ≤ 64 * (2 ^ Nat.clog 2 m) * (2 ^ Nat.clog 2 N) := by gcongr
    _ = 2 ^ (6 + Nat.clog 2 m + Nat.clog 2 N) := by
      simp only [pow_add]
      norm_num

theorem sampled_detuning_probability (s : Finset ℝ) (m N : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) (hcount : s.card ≤ N) :
    Maxwell.Continuum.DetuningGrid.gridProbability (gridSize m N)
      (grid_pos m N _ hm hN (gridSize_sufficient m N))
      (badDraws s τ (radius m N τ) (gridSize m N)) ≤ 3 / (64 * (m : ℝ)) :=
  finite_detuning_probability s m N _ τ hm hN hτ hcount (gridSize_sufficient m N)

/-- Every possible sample lies strictly inside the allowed interval. -/
theorem sample_mem (m N j : ℕ) (τ : ℝ) (hτ : 0 < τ) (hj : j < gridSize m N) :
    0 < Maxwell.Continuum.DetuningGrid.midpoint τ (gridSize m N) j ∧
      Maxwell.Continuum.DetuningGrid.midpoint τ (gridSize m N) j < τ :=
  Maxwell.Continuum.DetuningGrid.midpoint_mem τ _ j hτ hj

/-- A dyadic interval width yields an exact dyadic shift, with an explicitly
bounded denominator exponent. -/
theorem sample_dyadic (a : ℤ) (p m N j : ℕ) :
    Maxwell.Continuum.DetuningGrid.midpoint ((a : ℝ) / 2^p) (gridSize m N) j =
      (((2 * (j : ℤ) + 1) * a : ℤ) : ℝ) / 2^(p + randomBits m N + 1) :=
  Maxwell.Continuum.DetuningGrid.midpoint_dyadic a p (randomBits m N) j

end
end Maxwell.Continuum.Detuning
