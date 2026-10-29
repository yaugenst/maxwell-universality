import Maxwell.Continuum.Detuning

/-!
# From a local spectral count to a global detuning gap

The set `S` below can be the real spectrum of an unbounded self-adjoint
operator; it need not be finite. Only its part in `[-1/4, 1/4]` must be covered
by the finite set supplied to the detuning bound. All geometric and counting
steps are proved here. Establishing the spectrum and local count for the
actual PEC Maxwell operator is a separate analytic obligation.
-/

namespace Maxwell.Continuum.Detuning

noncomputable section
open scoped Classical

theorem radius_le_tau (m N : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) :
    radius m N τ ≤ τ := by
  have hden : 1 ≤ 64 * m * N := by
    have h : 0 < 64 * m * N := by positivity
    omega
  have hdenR : (1 : ℝ) ≤ 64 * m * N := by exact_mod_cast hden
  exact div_le_self hτ.le hdenR

/-- The small detuning interval and its exclusion radius cannot encounter
spectral values outside the fixed counting window. -/
theorem near_midpoint_mem_window (m N J j : ℕ) (τ eig : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64)
    (hj : j < J)
    (hnear : |eig - DetuningGrid.midpoint τ J j| < radius m N τ) :
    eig ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) := by
  have hsample := DetuningGrid.midpoint_mem τ J j hτ hj
  have hr := radius_le_tau m N τ hm hN hτ
  have habs := abs_lt.mp hnear
  constructor <;> linarith

/-- Every point outside the counting window is at least the inverse-budget
distance from every allowed sample. -/
theorem outside_window_gap (m N J j : ℕ) (τ eig : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64)
    (hj : j < J) (hout : eig ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) :
    radius m N τ ≤ |eig - DetuningGrid.midpoint τ J j| := by
  by_contra h
  exact hout (near_midpoint_mem_window m N J j τ eig hm hN hτ hτupper hj
    (lt_of_not_ge h))

/-- The actual bad event for an arbitrary, possibly infinite, real spectrum. -/
def spectrumBadDraws (S : Set ℝ) (τ r : ℝ) (J : ℕ) : Finset ℕ :=
  (Finset.range J).filter fun j =>
    ∃ eig ∈ S, |eig - DetuningGrid.midpoint τ J j| < r

@[simp] theorem mem_spectrumBadDraws (S : Set ℝ) (τ r : ℝ) (J j : ℕ) :
    j ∈ spectrumBadDraws S τ r J ↔
      j < J ∧ ∃ eig ∈ S, |eig - DetuningGrid.midpoint τ J j| < r := by
  simp [spectrumBadDraws]

theorem spectrumBadDraws_subset (S : Set ℝ) (τ r : ℝ) (J : ℕ) :
    spectrumBadDraws S τ r J ⊆ Finset.range J := Finset.filter_subset _ _

/-- Covering the spectrum in the fixed window suffices to cover every bad
sample, although spectrum outside that window can be infinite. -/
theorem spectrumBadDraws_subset_badDraws (S : Set ℝ) (s : Finset ℝ)
    (m N J : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64)
    (hlocal : ∀ eig ∈ S, eig ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → eig ∈ s) :
    spectrumBadDraws S τ (radius m N τ) J ⊆ badDraws s τ (radius m N τ) J := by
  intro j hj
  obtain ⟨hjJ, eig, heig, hnear⟩ := (mem_spectrumBadDraws _ _ _ _ _).mp hj
  apply (mem_badDraws _ _ _ _ _).mpr
  exact ⟨hjJ, eig, hlocal eig heig
    (near_midpoint_mem_window m N J j τ eig hm hN hτ hτupper hjJ hnear), hnear⟩

/-- The finite counting theorem controls the true spectral-gap failure event.
This theorem takes a local spectral cover and count, not a probability premise. -/
theorem spectrum_detuning_probability (S : Set ℝ) (s : Finset ℝ)
    (m N J : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64)
    (hcount : s.card ≤ N) (hgrid : 64 * m * N ≤ J)
    (hlocal : ∀ eig ∈ S, eig ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → eig ∈ s) :
    DetuningGrid.gridProbability J (grid_pos m N J hm hN hgrid)
      (spectrumBadDraws S τ (radius m N τ) J) ≤ 3 / (64 * (m : ℝ)) := by
  rw [DetuningGrid.gridProbability_eq _ _ _ (spectrumBadDraws_subset _ _ _ _)]
  calc
    ((spectrumBadDraws S τ (radius m N τ) J).card : ℝ) / J ≤
        ((badDraws s τ (radius m N τ) J).card : ℝ) / J := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg J)
      exact_mod_cast Finset.card_le_card
        (spectrumBadDraws_subset_badDraws S s m N J τ hm hN hτ hτupper hlocal)
    _ ≤ 3 / (64 * (m : ℝ)) :=
      finite_detuning_fraction s m N J τ hm hN hτ hcount hgrid

/-- On the complement of the true bad event, every spectral point has the
required gap. No inverse theorem is hidden in this elementary conclusion. -/
theorem gap_of_not_spectrumBadDraws (S : Set ℝ) (m N J j : ℕ) (τ : ℝ)
    (hj : j < J) (hgood : j ∉ spectrumBadDraws S τ (radius m N τ) J) :
    ∀ eig ∈ S, 1 / inverseBudget m N τ ≤ |eig - DetuningGrid.midpoint τ J j| := by
  intro eig heig
  rw [← radius_eq_inverseBudget_inv]
  by_contra h
  exact hgood ((mem_spectrumBadDraws _ _ _ _ _).mpr
    ⟨hj, eig, heig, lt_of_not_ge h⟩)

/-- A good draw for the finite cover is a good draw for the full spectrum. -/
theorem gap_of_not_badDraws (S : Set ℝ) (s : Finset ℝ)
    (m N J j : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64)
    (hlocal : ∀ eig ∈ S, eig ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → eig ∈ s)
    (hj : j < J) (hgood : j ∉ badDraws s τ (radius m N τ) J) :
    ∀ eig ∈ S, 1 / inverseBudget m N τ ≤ |eig - DetuningGrid.midpoint τ J j| := by
  apply gap_of_not_spectrumBadDraws S m N J j τ hj
  exact fun hbad => hgood
    (spectrumBadDraws_subset_badDraws S s m N J τ hm hN hτ hτupper hlocal hbad)

end
end Maxwell.Continuum.Detuning
