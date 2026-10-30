import Maxwell.Continuum.WellCutoffDeriv

/-! A fixed smooth unit-width boundary ramp, with symbolic derivative
bounds. This gives an explicit smooth choice for the finite-box cutoff. -/

noncomputable section

namespace Maxwell.Continuum.BoxCutoff

open Set Filter
open scoped Topology

def ramp (x : ℝ) : ℝ := if x ≤ 2 then Well.psi (3-x) else 1

theorem ramp_nonneg (x : ℝ) : 0 ≤ ramp x := by
  unfold ramp
  split_ifs
  · exact Well.psi_nonneg _
  · norm_num

theorem ramp_le_one (x : ℝ) : ramp x ≤ 1 := by
  unfold ramp
  split_ifs
  · exact Well.psi_le_one _
  · exact le_rfl

theorem ramp_zero {x : ℝ} (hx : x ≤ 1) : ramp x = 0 := by
  rw [ramp, ite_eq_left (by linarith)]
  exact Well.psi_eq_zero_of_two_le _ (by rw [abs_of_nonneg (by linarith)]; linarith)

theorem ramp_one {x : ℝ} (hx : 2 ≤ x) : ramp x = 1 := by
  unfold ramp
  split_ifs with h
  · apply Well.psi_eq_one
    rw [abs_le]
    constructor <;> linarith
  · rfl

theorem ramp_eq_psi {x : ℝ} (hx : x < 3) : ramp x = Well.psi (3-x) := by
  unfold ramp
  split_ifs with h
  · rfl
  · symm
    apply Well.psi_eq_one
    rw [abs_le]
    constructor <;> linarith

theorem ramp_eventually_psi {x : ℝ} (hx : x < 3) :
    ramp =ᶠ[𝓝 x] fun y => Well.psi (3-y) :=
  (eventually_lt_nhds hx).mono fun _ hy => ramp_eq_psi hy

theorem ramp_eventually_one {x : ℝ} (hx : 2 < x) :
    ramp =ᶠ[𝓝 x] fun _ => 1 :=
  (eventually_gt_nhds hx).mono fun _ hy => ramp_one hy.le

theorem ramp_contDiff : ContDiff ℝ (⊤ : ℕ∞) ramp := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < 3
  · exact (Well.psi_contDiff.comp (contDiff_const.sub contDiff_id)).contDiffAt.congr_of_eventuallyEq
      (ramp_eventually_psi hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (ramp_eventually_one (by linarith))

theorem ramp_iteratedDeriv_bound (K : ℕ) (x : ℝ) :
    |iteratedDeriv (K+1) ramp x| ≤ 16*(800 : ℝ)^K*(K.factorial : ℝ)^2 := by
  by_cases hx : x < 3
  · rw [(ramp_eventually_psi hx).iteratedDeriv_eq (K+1), iteratedDeriv_comp_const_sub]
    simpa only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      Well.psi_iteratedDeriv_succ_bound K (3-x)
  · rw [(ramp_eventually_one (by linarith : 2 < x)).iteratedDeriv_eq (K+1), iteratedDeriv_const]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, abs_zero]
    positivity

theorem ramp_deriv_bound (x : ℝ) : |deriv ramp x| ≤ 16 := by
  simpa only [Nat.zero_add, iteratedDeriv_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, one_pow, mul_one] using ramp_iteratedDeriv_bound 0 x

theorem ramp_second_bound (x : ℝ) : |deriv (deriv ramp) x| ≤ 12800 := by
  have h := ramp_iteratedDeriv_bound 1 x
  norm_num [iteratedDeriv_succ, iteratedDeriv_zero] at h
  exact h

#print axioms ramp_iteratedDeriv_bound

end Maxwell.Continuum.BoxCutoff
