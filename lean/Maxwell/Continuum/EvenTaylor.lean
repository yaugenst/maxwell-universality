import Maxwell.Continuum.CauchyBounds
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-! The quantitative even Taylor remainder used by the band-edge expansion.
The odd coefficients vanish by local reflection symmetry; the remaining tail
is bounded by an actual convergent geometric series. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EvenTaylor

open Set Metric Filter
open scoped Topology

def coefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0

theorem odd_deriv_zero {f : ℂ → ℂ}
    (heven : (fun z => f (-z)) =ᶠ[𝓝 0] f) (n : ℕ) :
    iteratedDeriv (2 * n + 1) f 0 = 0 := by
  have h := heven.iteratedDeriv_eq (2 * n + 1)
  rw [iteratedDeriv_comp_neg, neg_zero] at h
  have hp : (-1 : ℂ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hp, neg_one_smul] at h
  linear_combination -(1 / 2 : ℂ) * h

theorem odd_coefficient_zero {f : ℂ → ℂ}
    (heven : (fun z => f (-z)) =ᶠ[𝓝 0] f) (n : ℕ) :
    coefficient f (2 * n + 1) = 0 := by
  simp only [coefficient, odd_deriv_zero heven n, mul_zero]

theorem coefficient_norm_le {f : ℂ → ℂ} {R C : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hC : ∀ z ∈ ball 0 R, ‖f z‖ ≤ C) (hR : 0 < R) (n : ℕ) :
    ‖coefficient f n‖ ≤ C / R ^ n := by
  have hd := CauchyBounds.norm_iteratedDeriv_zero_le_of_open n hf hC hR
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [coefficient, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ) * C / R ^ n) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = C / R ^ n := by field_simp

theorem hasSum_coefficients {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R)) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun n => coefficient f n * z ^ n) (f z) := by
  have h := Complex.hasSum_taylorSeries_on_ball
    hf.differentiableOn
    (by simpa only [mem_ball, dist_zero_right] using hz)
  convert h using 1
  funext n
  simp only [coefficient, sub_zero, smul_eq_mul]
  ring

theorem hasSum_even_coefficients {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (heven : (fun z => f (-z)) =ᶠ[𝓝 0] f) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun n => coefficient f (2 * n) * z ^ (2 * n)) (f z) := by
  have hs := hasSum_coefficients hf hz
  have hsi : Function.Injective (fun n : ℕ => 2 * n) := by
    intro m n h
    dsimp at h
    omega
  have hse := hs.summable.comp_injective hsi
  have hso : HasSum (fun n => coefficient f (2 * n + 1) * z ^ (2 * n + 1)) 0 := by
    simpa only [odd_coefficient_zero heven, zero_mul] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have hsum := HasSum.even_add_odd (f := fun n => coefficient f n * z ^ n) hse.hasSum hso
  have heq := hsum.unique hs
  rw [add_zero] at heq
  exact heq ▸ hse.hasSum

theorem remainder_bound {f : ℂ → ℂ} {R C : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hC : ∀ z ∈ ball 0 R, ‖f z‖ ≤ C) (hR : 0 < R)
    (heven : (fun z => f (-z)) =ᶠ[𝓝 0] f) {z : ℂ} (hz : ‖z‖ < R) :
    ‖f z - f 0 - coefficient f 2 * z ^ 2‖ ≤
      C * (‖z‖ / R) ^ 4 / (1 - (‖z‖ / R) ^ 2) := by
  have ha : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR.le
  have ha' : ‖z‖ / R < 1 := (div_lt_one hR).mpr hz
  have har : (‖z‖ / R) ^ 2 < 1 := by nlinarith
  have hbound (n : ℕ) : ‖coefficient f (2 * n) * z ^ (2 * n)‖ ≤
      C * ((‖z‖ / R) ^ 2) ^ n := by
    rw [norm_mul, norm_pow]
    calc
      _ ≤ (C / R ^ (2 * n)) * ‖z‖ ^ (2 * n) :=
        mul_le_mul_of_nonneg_right (coefficient_norm_le hf hC hR _) (by positivity)
      _ = C * ((‖z‖ / R) ^ 2) ^ n := by rw [← pow_mul, div_pow]; ring
  have h := norm_sub_le_of_geometric_bound_of_hasSum har hbound
    (hasSum_even_coefficients hf heven hz) 2
  have hpartial : (∑ n ∈ Finset.range 2, coefficient f (2 * n) * z ^ (2 * n)) =
      f 0 + coefficient f 2 * z ^ 2 := by
    simp [Finset.sum_range_succ, coefficient, iteratedDeriv_zero]
  rw [hpartial, norm_sub_rev] at h
  convert h using 1 <;> ring_nf

theorem quartic_bound {f : ℂ → ℂ} {R ρ : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hC : ∀ z ∈ ball 0 R, ‖f z‖ ≤ 3 * ρ) (hR : 0 < R) (hρ : 0 ≤ ρ)
    (heven : (fun z => f (-z)) =ᶠ[𝓝 0] f) {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖f z - f 0 - coefficient f 2 * z ^ 2‖ ≤ 4 * ρ * R⁻¹ ^ 4 * ‖z‖ ^ 4 := by
  have hz' : ‖z‖ < R := by linarith
  have ha : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR.le
  have ha' : ‖z‖ / R ≤ 1 / 2 := (div_le_iff₀ hR).mpr (by linarith)
  have hsq : (‖z‖ / R) ^ 2 ≤ 1 / 4 := by nlinarith
  have hden : 0 < 1 - (‖z‖ / R) ^ 2 := by linarith
  refine (remainder_bound hf hC hR heven hz').trans ?_
  have hmul : (3 * ρ) * (‖z‖ / R) ^ 4 / (1 - (‖z‖ / R) ^ 2) ≤
      4 * ρ * (‖z‖ / R) ^ 4 := by
    apply (div_le_iff₀ hden).mpr
    have hnon : 0 ≤ ρ * (‖z‖ / R) ^ 4 := by positivity
    nlinarith
  exact hmul.trans_eq (by rw [div_pow, div_eq_mul_inv, inv_pow]; ring)

end Maxwell.Continuum.EvenTaylor
