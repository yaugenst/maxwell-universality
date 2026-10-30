import Maxwell.Continuum.CutoffIntegralWidths
import Maxwell.Continuum.CutoffProductEvaluation

/-! Polynomial word widths for the finite scalar and three-dimensional cutoff evaluators. -/

namespace Maxwell.Continuum.Calibration

open RationalWords Profile

set_option maxHeartbeats 800000
attribute [local irreducible] cutoffIntegralApprox cutoffDenominatorApprox psiNumeratorApprox psiCenter

theorem cutoff_half_width : Width (1/2 : ℚ) 2 := by
  have h := width_fraction (z := 1) (d := 2) (B := 2) (by decide) (by decide) (by decide)
  simpa only [Int.cast_one,Nat.cast_ofNat] using h

theorem cutoffIntegralWidth_mono (N : ℕ) {V W : ℕ} (h : V≤W) :
    cutoffIntegralWidth N V≤cutoffIntegralWidth N W := by
  unfold cutoffIntegralWidth
  gcongr

theorem cutoffClampRat_width {q : ℚ} {W : ℕ} (hq : Width q W) :
    Width (cutoffClampRat q) (W+2) := by
  have hh := cutoff_half_width
  have hh' : Width (-1/2 : ℚ) (W+2) := by
    simpa only [neg_div] using hh.neg.mono (show 2≤W+2 by omega)
  unfold cutoffClampRat
  by_cases h : (1/2 : ℚ)≤q
  · rw [min_eq_left h,max_eq_right (by norm_num : (-1/2 : ℚ)≤1/2)]
    exact hh.mono (by omega)
  · rw [min_eq_right (le_of_not_ge h)]
    by_cases hlo : (-1/2 : ℚ)≤q
    · rw [max_eq_right hlo]
      exact hq.mono (by omega)
    · rw [max_eq_left (le_of_not_ge hlo)]
      exact hh'

theorem cutoffDenominatorApprox_width (N : ℕ) :
    Width (cutoffDenominatorApprox N) (cutoffIntegralWidth N 2) := by
  unfold cutoffDenominatorApprox
  exact cutoffIntegralApprox_width (by simpa only [neg_div] using cutoff_half_width.neg) cutoff_half_width N

theorem psiNumeratorApprox_width {q : ℚ} {W : ℕ} (hq : Width q W) (N : ℕ) :
    Width (psiNumeratorApprox q N) (cutoffIntegralWidth N (W+6)) := by
  have hh : Width (3/2 : ℚ) 3 := by
    have h := width_fraction (z := 3) (d := 2) (B := 3) (by decide) (by decide) (by decide)
    simpa only [Int.cast_ofNat,Nat.cast_ofNat] using h
  unfold psiNumeratorApprox
  exact cutoffIntegralApprox_width (cutoffClampRat_width (hq.sub hh))
    (cutoffClampRat_width (hq.add hh)) N

theorem psiCenter_width {q : ℚ} {W : ℕ} (hq : Width q W) (N : ℕ) :
    Width (psiCenter q N) (2*cutoffIntegralWidth N (W+6)) := by
  have hd := cutoffDenominatorApprox_width N
  have hn := psiNumeratorApprox_width hq N
  have hd0 : cutoffDenominatorApprox N≠0 := by
    have h := cutoffDenominatorApprox_lower N
    linarith
  have h := hn.mul (hd.inv hd0)
  rw [← div_eq_mul_inv] at h
  unfold psiCenter
  exact h.mono (by have := cutoffIntegralWidth_mono N (show 2≤W+6 by omega); omega)

theorem chiCenter_width {q : Fin 3 → ℚ} {W : ℕ} (hq : ∀ i, Width (q i) W) (N : ℕ) :
    Width (chiCenter q N) (6*cutoffIntegralWidth N (W+6)) := by
  have h := ((psiCenter_width (hq 0) N).mul (psiCenter_width (hq 1) N)).mul
    (psiCenter_width (hq 2) N)
  simpa only [chiCenter,Fin.prod_univ_three,show
    2*cutoffIntegralWidth N (W+6)+2*cutoffIntegralWidth N (W+6)+2*cutoffIntegralWidth N (W+6)=
      6*cutoffIntegralWidth N (W+6) by omega] using h

theorem cutoffIntegralWidth_polynomial (N W : ℕ) :
    cutoffIntegralWidth N W≤2^100*(N+1)^6*(W+1) := by
  have hD := profileDegree_bound N
  have hN2 : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hDp : profileDegree N+1≤2^31*(N+1)^2 := by nlinarith only [hD,hN2]
  have hs := Nat.pow_le_pow_left hDp 2
  have hN4 : N+1≤(N+1)^4 := le_self_pow₀ (by omega : 1≤N+1) (by decide : (4 : ℕ)≠0)
  have hN4' : 1≤(N+1)^4 := one_le_pow₀ (by omega)
  have hm : 1≤(N+1)^4*(W+1) := Nat.succ_le_of_lt (by positivity)
  have hn : N+1≤(N+1)^4*(W+1) := hN4.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hterm : 272*(N+1)+18*(profileDegree N+1)^2*(W+1)+1≤
      2^67*(N+1)^4*(W+1) := by
    have hh := Nat.mul_le_mul_right (18*(W+1)) hs
    nlinarith only [hh,hn,hm]
  have hp := Nat.mul_le_mul hD hterm
  have hbig : 1≤(N+1)^6*(W+1) := Nat.succ_le_of_lt (by positivity)
  unfold cutoffIntegralWidth
  nlinarith only [hp,hbig]

theorem chiCenter_width_polynomial {q : Fin 3 → ℚ} {W : ℕ}
    (hq : ∀ i, Width (q i) W) (N : ℕ) :
    Width (chiCenter q N) (2^103*(N+1)^6*(W+7)) := by
  apply (chiCenter_width hq N).mono
  have h := Nat.mul_le_mul_left 6 (cutoffIntegralWidth_polynomial N (W+6))
  nlinarith only [h,Nat.zero_le ((N+1)^6*(W+7))]

#print axioms chiCenter_width_polynomial

end Maxwell.Continuum.Calibration
