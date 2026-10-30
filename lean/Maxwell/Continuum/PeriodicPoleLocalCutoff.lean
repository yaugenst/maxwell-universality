import Maxwell.Continuum.PoleSpaceCoordinates
import Maxwell.Continuum.PeriodicScaledCutoff

/-! On the literal local pole chart the almost-analytic Bloch cutoff
is exactly one. Every nonconstant Taylor term vanishes there. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192

namespace Maxwell.Continuum.AlmostAnalytic

open PeriodicBand

theorem cutoffTaylor_eq_one_inner (K : ℕ) (β : Space) (s : ℝ) {q : Space}
    (hq : ‖q‖ < smallRadius) : cutoffTaylor K smallRadius q β s = 1 := by
  unfold cutoffTaylor
  rw [Finset.sum_eq_single 0]
  · simp only [coefficient, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      Well.directionalDerivative, iteratedFDeriv_zero_apply]
    exact_mod_cast Auxiliary.cutoff_eq_one_of_norm_le hq.le
  · intro n _ hn
    change coefficient n s * (cutoffDerivative n β q : ℂ) = 0
    rw [cutoffDerivative_zero_inner hn β hq, Complex.ofReal_zero, mul_zero]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.zero_lt_succ K))).elim

end Maxwell.Continuum.AlmostAnalytic

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

theorem poleChartCutoff_ne_zero_norm {j : Fin 3} {k : Space}
    (hk : poleChartCutoff j k ≠ 0) : ‖k‖ ≤ 6*poleLongitudinalScale := by
  have hp := mul_ne_zero_iff.mp hk
  have hc (i : Fin 3) : |k i| ≤ 2*poleLongitudinalScale := by
    by_cases hi : i = j
    · subst i
      have hs := scaledPsi_support poleCutoff_scales.1 hp.1
      exact abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hi
      have hn : scaledPsi poleTransverseScale (k (j.succAbove l)) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hp.2) l (Finset.mem_univ _)
      have hs := scaledPsi_support poleCutoff_scales.2.1 hn
      exact (abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩).trans
        (mul_le_mul_of_nonneg_left poleCutoff_scales.2.2.2.2.1 (by norm_num))
  have hs : ‖k‖^2 ≤ 3*(2*poleLongitudinalScale)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, (2*poleLongitudinalScale)^2 := by
        apply Finset.sum_le_sum
        intro i _
        have he := (sq_le_sq₀ (abs_nonneg (k i))
          (mul_nonneg (by norm_num) poleCutoff_scales.1.le)).mpr (hc i)
        simpa only [sq_abs] using he
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  nlinarith only [hs, norm_nonneg k, poleCutoff_scales.1]

theorem poleChartCutoff_physical_inner {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) {j : Fin 3} {k : Space}
    (hk : poleChartCutoff j k ≠ 0) : ‖h • k‖ < smallRadius := by
  have hh1 : h ≤ 1 := hh.trans (div_le_self (by norm_num) (one_le_pow₀ (by norm_num)))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos D.h_pos]
  exact (mul_le_of_le_one_left (norm_nonneg k) hh1).trans_lt
    ((poleChartCutoff_ne_zero_norm hk).trans_lt (by norm_num [poleLongitudinalScale, smallRadius, backgroundAmplitude]))

theorem scaledPoleCutoff_eq_one_local {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) {j : Fin 3} {k : Space}
    (hk : poleChartCutoff j k ≠ 0) : scaledPoleCutoff D hh j k = 1 :=
  AlmostAnalytic.cutoffTaylor_eq_one_inner _ _ _ (poleChartCutoff_physical_inner D hh hk)

#print axioms scaledPoleCutoff_eq_one_local

end Maxwell.Continuum.PeriodicBand
