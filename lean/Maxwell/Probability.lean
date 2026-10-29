import Maxwell.Probability.Spectral
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Finite uniform midpoint detuning, with cardinality bounds at the full
finite matrix dimension. All estimates count the emitted finite grid itself. -/

namespace Maxwell.Probability

noncomputable section
open Finset
open scoped Classical

/-- The exact midpoint grid, before interpreting its uniform finite law. -/
def midpoint (τ : ℝ) (J j : ℕ) : ℝ := ((j : ℝ) + 1 / 2) * τ / J

/-- A single real spectral value's exceptional grid indices. -/
def nearGrid (τ radius eig : ℝ) (J : ℕ) : Finset ℕ :=
  (Finset.range J).filter (fun j => |eig - midpoint τ J j| < radius)

/-- Counting a finite subset of the integers uses only its extreme points. -/
theorem nat_card_le_span (s : Finset ℕ) (hs : s.Nonempty) :
    s.card ≤ s.max' hs + 1 - s.min' hs := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨s.min'_le i hi, s.le_max' i hi⟩
  simpa only [Nat.card_Icc] using Finset.card_le_card hsub

/-- The interval occupancy estimate, including endpoints conservatively. -/
theorem nearGrid_card_le (τ radius eig : ℝ) (J : ℕ)
    (hτ : 0 < τ) (hradius : 0 ≤ radius) (hJ : 0 < J) :
    ((nearGrid τ radius eig J).card : ℝ) ≤ 2 * radius * J / τ + 1 := by
  let s := nearGrid τ radius eig J
  by_cases hs : s.Nonempty
  · have hmin := (Finset.mem_filter.mp (s.min'_mem hs)).2
    have hmax := (Finset.mem_filter.mp (s.max'_mem hs)).2
    have hext : s.min' hs ≤ s.max' hs := s.min'_le _ (s.max'_mem hs)
    have hc := nat_card_le_span s hs
    have hcR : (s.card : ℝ) ≤ (s.max' hs : ℝ) + 1 - (s.min' hs : ℝ) := by
      have hcR := (Nat.cast_le (α := ℝ)).mpr hc
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hcR
      exact hcR
    have hgap : ((s.max' hs : ℝ) - (s.min' hs : ℝ)) * τ / J < 2 * radius := by
      have ha := (abs_lt.mp hmin).2
      have hb := (abs_lt.mp hmax).1
      have heq : ((s.max' hs : ℝ) - (s.min' hs : ℝ)) * τ / J =
          midpoint τ J (s.max' hs) - midpoint τ J (s.min' hs) := by
        dsimp [midpoint]; ring
      rw [heq]
      linarith
    have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
    have hspan : (s.max' hs : ℝ) - (s.min' hs : ℝ) ≤ 2 * radius * J / τ := by
      apply (le_div_iff₀ hτ).mpr
      exact le_of_lt ((div_lt_iff₀ hJR).mp hgap)
    exact hcR.trans (by linarith)
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hnonneg : 0 ≤ 2 * radius * (J : ℝ) / τ := by positivity
    simpa [s, hempty] using (show (0 : ℝ) ≤ 2 * radius * (J : ℝ) / τ + 1 by linarith)

/-- The bad event is a union over the complete finite spectrum. -/
def spectralBad {N : ℕ} (eigenvalues : Fin N → ℝ)
    (τ radius : ℝ) (J : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => nearGrid τ radius (eigenvalues i) J)

@[simp] theorem mem_spectralBad {N : ℕ} (eigenvalues : Fin N → ℝ)
    (τ radius : ℝ) (J j : ℕ) :
    j ∈ spectralBad eigenvalues τ radius J ↔
      j < J ∧ ∃ i, |eigenvalues i - midpoint τ J j| < radius := by
  simp [spectralBad, nearGrid, exists_and_left]

theorem spectralBad_subset {N : ℕ} (eigenvalues : Fin N → ℝ)
    (τ radius : ℝ) (J : ℕ) :
    spectralBad eigenvalues τ radius J ⊆ Finset.range J := by
  intro j hj
  exact Finset.mem_range.mpr ((mem_spectralBad _ _ _ _ _).mp hj).1

theorem spectralBad_card_le {N : ℕ} (eigenvalues : Fin N → ℝ)
    (τ radius : ℝ) (J : ℕ) (hτ : 0 < τ) (hradius : 0 ≤ radius) (hJ : 0 < J) :
    ((spectralBad eigenvalues τ radius J).card : ℝ) ≤
      N * (2 * radius * J / τ + 1) := by
  calc
    ((spectralBad eigenvalues τ radius J).card : ℝ) ≤
        ∑ i : Fin N, ((nearGrid τ radius (eigenvalues i) J).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin N)))
        (t := fun i => nearGrid τ radius (eigenvalues i) J))
    _ ≤ ∑ _ : Fin N, (2 * radius * J / τ + 1) :=
      Finset.sum_le_sum (fun i _ => nearGrid_card_le τ radius (eigenvalues i) J hτ hradius hJ)
    _ = N * (2 * radius * J / τ + 1) := by simp; ring

/-- The actual uniform finite distribution, rather than a probability premise. -/
def gridLaw (J : ℕ) (hJ : 0 < J) : PMF ℕ :=
  PMF.uniformOfFinset (Finset.range J) (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hJ))

/-- Exact probability, as a real number, under the finite law. -/
def gridProbability (J : ℕ) (hJ : 0 < J) (event : Finset ℕ) : ℝ :=
  ((gridLaw J hJ).toOuterMeasure (event : Set ℕ)).toReal

theorem gridProbability_eq (J : ℕ) (hJ : 0 < J) (event : Finset ℕ)
    (hevent : event ⊆ Finset.range J) :
    gridProbability J hJ event = (event.card : ℝ) / J := by
  classical
  unfold gridProbability gridLaw
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Finset.card_range, ENNReal.toReal_div, ENNReal.toReal_natCast]
  congr 2
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_coe, and_iff_right_iff_imp]
  exact fun hj => hevent hj

theorem spectralBad_probability_le {N : ℕ} (eigenvalues : Fin N → ℝ)
    (τ radius : ℝ) (J : ℕ) (hτ : 0 < τ) (hradius : 0 ≤ radius) (hJ : 0 < J) :
    gridProbability J hJ (spectralBad eigenvalues τ radius J) ≤
      2 * N * radius / τ + N / J := by
  rw [gridProbability_eq _ _ _ (spectralBad_subset _ _ _ _)]
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  calc
    ((spectralBad eigenvalues τ radius J).card : ℝ) / J ≤
        (N * (2 * radius * J / τ + 1)) / J :=
      div_le_div_of_nonneg_right (spectralBad_card_le _ _ _ _ hτ hradius hJ) hJR.le
    _ = 2 * N * radius / τ + N / J := by field_simp

/-- The radius used for the final finite box is `1 / L_b`. -/
def detuningRadius (m N : ℕ) (τ : ℝ) : ℝ := τ / (16 * (m + N : ℝ)^2)

/-- The exact bound in the paper, with `N` the complete emitted matrix dimension. -/
theorem finite_detuning_probability {N : ℕ} (eigenvalues : Fin N → ℝ)
    (m J : ℕ) (τ : ℝ) (hm : 0 < m) (hτ : 0 < τ)
    (hgrid : 16 * (m + N)^2 ≤ J) :
    ∃ hJ : 0 < J,
      gridProbability J hJ (spectralBad eigenvalues τ (detuningRadius m N τ) J) ≤
        3 * N / (16 * (m + N : ℝ)^2) ∧
      3 * N / (16 * (m + N : ℝ)^2) ≤ 3 / (64 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : (0 : ℝ) < m + N := by positivity
  have hden : (0 : ℝ) < 16 * (m + N : ℝ)^2 := by positivity
  have hgridR : 16 * (m + N : ℝ)^2 ≤ J := by exact_mod_cast hgrid
  have hJR : (0 : ℝ) < J := hden.trans_le hgridR
  have hJ : 0 < J := by exact_mod_cast hJR
  refine ⟨hJ, ?_, ?_⟩
  · have hraw := spectralBad_probability_le eigenvalues τ (detuningRadius m N τ) J
      hτ (by dsimp [detuningRadius]; positivity) hJ
    have hinv : (N : ℝ) / J ≤ N / (16 * (m + N : ℝ)^2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg N) hden hgridR
    have heq : 2 * (N : ℝ) * detuningRadius m N τ / τ =
        2 * N / (16 * (m + N : ℝ)^2) := by
      dsimp [detuningRadius]
      field_simp
    rw [heq] at hraw
    calc
      _ ≤ 2 * N / (16 * (m + N : ℝ)^2) + N / J := hraw
      _ ≤ 2 * N / (16 * (m + N : ℝ)^2) + N / (16 * (m + N : ℝ)^2) :=
        by linarith
      _ = 3 * N / (16 * (m + N : ℝ)^2) := by ring
  · apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < 64 * m)).mpr
    nlinarith [sq_nonneg ((m : ℝ) - N)]

/-- Every sample lies strictly inside the prescribed detuning interval. -/
theorem midpoint_mem (τ : ℝ) (J j : ℕ) (hτ : 0 < τ) (hj : j < J) :
    0 < midpoint τ J j ∧ midpoint τ J j < τ := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (Nat.zero_le j).trans_lt hj
  have hjR : (j : ℝ) + 1 ≤ J := by exact_mod_cast hj
  dsimp [midpoint]
  constructor
  · positivity
  · apply (div_lt_iff₀ hJ).mpr
    nlinarith

/-- The finite-background inverse budget. -/
def inverseBudget (m N : ℕ) (τ : ℝ) : ℝ := 16 * (m + N : ℝ)^2 / τ

theorem detuningRadius_eq_inverseBudget_inv (m N : ℕ) (τ : ℝ) :
    detuningRadius m N τ = 1 / inverseBudget m N τ := by
  simp [detuningRadius, inverseBudget, div_eq_mul_inv]

/-- The exceptional event includes every singular shifted matrix, since its
complement requires a two-sided inverse as well as its Euclidean norm bound. -/
def matrixBad {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (τ L : ℝ)
    (J : ℕ) : Finset ℕ :=
  (Finset.range J).filter fun j =>
    ¬ InverseBound (A - midpoint τ J j • (1 : Matrix (Fin N) (Fin N) ℝ)) L

theorem matrixBad_subset_spectralBad {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (τ L : ℝ) (J : ℕ) (hL : 0 < L) :
    matrixBad A τ L J ⊆ spectralBad hA.eigenvalues τ (1 / L) J := by
  intro j hj
  obtain ⟨hjJ, hjbad⟩ := Finset.mem_filter.mp hj
  apply (mem_spectralBad _ _ _ _ _).mpr
  refine ⟨Finset.mem_range.mp hjJ, ?_⟩
  by_contra h
  push Not at h
  exact hjbad (shifted_inverseBound hA (midpoint τ J j) L hL h)

theorem gridProbability_mono (J : ℕ) (hJ : 0 < J) {s t : Finset ℕ}
    (hst : s ⊆ t) (ht : t ⊆ Finset.range J) :
    gridProbability J hJ s ≤ gridProbability J hJ t := by
  rw [gridProbability_eq _ _ _ (hst.trans ht), gridProbability_eq _ _ _ ht]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hst)
    (Nat.cast_nonneg J)

/-- Actual finite-matrix detuning theorem: the probability is evaluated under
the concrete uniform grid, and its event is failure of the inverse bound. -/
theorem finite_matrix_detuning {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (m J : ℕ) (τ : ℝ) (hm : 0 < m) (hτ : 0 < τ)
    (hgrid : 16 * (m + N)^2 ≤ J) :
    ∃ hJ : 0 < J,
      gridProbability J hJ (matrixBad A τ (inverseBudget m N τ) J) ≤
        3 * N / (16 * (m + N : ℝ)^2) ∧
      gridProbability J hJ (matrixBad A τ (inverseBudget m N τ) J) ≤
        3 / (64 * (m : ℝ)) := by
  obtain ⟨hJ, hprob, hsmall⟩ :=
    finite_detuning_probability hA.eigenvalues m J τ hm hτ hgrid
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : 0 < inverseBudget m N τ := by dsimp [inverseBudget]; positivity
  have hsub := matrixBad_subset_spectralBad hA τ (inverseBudget m N τ) J hL
  rw [← detuningRadius_eq_inverseBudget_inv] at hsub
  have hbound := (gridProbability_mono J hJ hsub (spectralBad_subset _ _ _ _)).trans hprob
  exact ⟨hJ, hbound, hbound.trans hsmall⟩

/-- The exact number of fair bits used to sample the detuning index. -/
def detuningBits (m N : ℕ) : ℕ := Nat.clog 2 (16 * (m + N)^2)

def detuningGridSize (m N : ℕ) : ℕ := 2 ^ detuningBits m N

theorem detuningGridSize_sufficient (m N : ℕ) :
    16 * (m + N)^2 ≤ detuningGridSize m N := Nat.le_pow_clog (by norm_num) _

/-- No retry or rejection sampler is needed: exactly this many fair bits
index a grid satisfying the theorem's lower bound. -/
theorem detuningBits_le (m N : ℕ) :
    detuningBits m N ≤ 4 + 2 * Nat.clog 2 (m + N) := by
  apply Nat.clog_le_of_le_pow
  have h := Nat.le_pow_clog (b := 2) (by norm_num) (m + N)
  calc
    16 * (m + N)^2 ≤ 16 * (2 ^ Nat.clog 2 (m + N))^2 := by gcongr
    _ = 2 ^ (4 + 2 * Nat.clog 2 (m + N)) := by
      rw [pow_add, Nat.mul_comm 2 (Nat.clog 2 (m + N)), pow_mul]
      norm_num

/-- With dyadic interval width, every emitted midpoint is itself an exact
dyadic with an explicitly bounded denominator exponent. -/
theorem midpoint_dyadic (a : ℤ) (p bits j : ℕ) :
    midpoint ((a : ℝ) / 2^p) (2^bits) j =
      (((2 * (j : ℤ) + 1) * a : ℤ) : ℝ) / 2^(p + bits + 1) := by
  simp only [midpoint, Nat.cast_pow, Nat.cast_ofNat, Int.cast_mul, Int.cast_add,
    Int.cast_ofNat, Int.cast_natCast, pow_add]
  field_simp
  ring

end
end Maxwell.Probability
