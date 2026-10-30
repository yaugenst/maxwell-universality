import Maxwell.Continuum.PoleChartCutoff

/-! Exact coordinate-line cutoffs and their first sixteen derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric TransverseGaussian
open scoped ContDiff

theorem poleChartCutoff_line (j : Fin 3) (q : Space) (t : ℝ) :
    poleChartCutoff j (q + t • PiLp.single 2 j 1) =
      scaledPsi poleLongitudinalScale (q j+t) *
        ∏ k : Fin 2, scaledPsi poleTransverseScale (q (j.succAbove k)) := by
  unfold poleChartCutoff poleLongitudinalCutoff
  congr 1
  · congr 1
    simp
  · apply Finset.prod_congr rfl
    intro k _
    congr 1
    simp [Fin.succAbove_ne]

theorem poleLongitudinal_derivative_bound {n : ℕ} (hn : n ≤ 16) (u : ℝ) :
    |iteratedDeriv n (scaledPsi poleLongitudinalScale) u| ≤ (2 : ℝ)^33060 := by
  have ha := poleCutoff_scales.1
  have hbase : 800/poleLongitudinalScale ≤ (2 : ℝ)^2058 := by
    unfold poleLongitudinalScale
    rw [div_inv_eq_mul, show 2058 = 10+2048 by omega, pow_add]
    exact mul_le_mul_of_nonneg_right (by norm_num : (800 : ℝ) ≤ 2^10) (by positivity)
  have hf : (n.factorial : ℝ) ≤ (2 : ℝ)^64 := by
    calc
      _ ≤ ((16 : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_le hn
      _ ≤ (16 : ℝ)^16 := by exact_mod_cast Nat.factorial_le_pow 16
      _ = _ := by rw [show (16 : ℝ)=2^4 by norm_num, ← pow_mul]
  have hp : (800/poleLongitudinalScale)^n ≤ ((2 : ℝ)^2058)^16 := by
    calc
      _ ≤ ((2 : ℝ)^2058)^n := pow_le_pow_left₀ (by positivity) hbase _
      _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hn
  calc
    _ ≤ 16*(800/poleLongitudinalScale)^n*(n.factorial : ℝ)^2 := scaledPsi_derivative_bound ha n u
    _ ≤ 16*((2 : ℝ)^2058)^16*((2 : ℝ)^64)^2 := by gcongr
    _ = _ := by rw [show (16 : ℝ)=2^4 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]

theorem poleChartCutoff_longitudinal_derivative (j : Fin 3) (q : Space) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => poleChartCutoff j (q+u • PiLp.single 2 j 1)) t =
      iteratedDeriv n (scaledPsi poleLongitudinalScale) (q j+t) *
        ∏ k : Fin 2, scaledPsi poleTransverseScale (q (j.succAbove k)) := by
  simp_rw [poleChartCutoff_line]
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_comp_const_add]

theorem poleChartCutoff_longitudinal_bound (j : Fin 3) (q : Space) {n : ℕ}
    (hn : n ≤ 16) (t : ℝ) :
    |iteratedDeriv n (fun u : ℝ => poleChartCutoff j (q+u • PiLp.single 2 j 1)) t| ≤
      (2 : ℝ)^70000 := by
  rw [poleChartCutoff_longitudinal_derivative, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg (fun _ _ => scaledPsi_nonneg _ _))]
  have hp := Finset.prod_le_one₀ (s := Finset.univ)
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin 2))) => scaledPsi_nonneg poleTransverseScale (q (j.succAbove k)))
    (fun k _ => scaledPsi_le_one poleTransverseScale (q (j.succAbove k)))
  calc
    _ ≤ |iteratedDeriv n (scaledPsi poleLongitudinalScale) (q j+t)| :=
      mul_le_of_le_one_right (abs_nonneg _) hp
    _ ≤ (2 : ℝ)^33060 := poleLongitudinal_derivative_bound hn _
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num)

theorem poleChartComplement_longitudinal_bound (j : Fin 3) (q : Space) {n : ℕ}
    (hn : n ≤ 16) (t : ℝ) :
    |iteratedDeriv n (fun u : ℝ => 1-poleChartCutoff j (q+u • PiLp.single 2 j 1)) t| ≤
      (2 : ℝ)^70000 := by
  by_cases hz : n = 0
  · subst n
    rw [iteratedDeriv_zero, abs_of_nonneg (sub_nonneg.mpr (poleChartCutoff_le_one _ _))]
    exact (show 1-poleChartCutoff j (q+t • PiLp.single 2 j 1) ≤ 1 by
      linarith only [poleChartCutoff_nonneg j (q+t • PiLp.single 2 j 1)]).trans
      (one_le_pow₀ (by norm_num))
  · rw [iteratedDeriv_const_sub (Nat.pos_of_ne_zero hz), iteratedDeriv_neg, abs_neg]
    exact poleChartCutoff_longitudinal_bound j q hn t

#print axioms poleChartComplement_longitudinal_bound

end Maxwell.Continuum.PeriodicBand
