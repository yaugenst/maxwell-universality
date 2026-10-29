import Maxwell.Continuum.AlmostAnalyticTaylor
import Mathlib.Analysis.Normed.Module.Normalize

/-! The literal Bloch cutoff's finite almost-analytic extension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex

theorem directionalDerivative_smul (K : ℕ) (f : Space → ℝ) (q v : Space) (r : ℝ) :
    Well.directionalDerivative K f q (r • v) = r^K * Well.directionalDerivative K f q v := by
  unfold Well.directionalDerivative
  rw [(iteratedFDeriv ℝ K f q).map_smul_univ (fun _ => r) (fun _ => v)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem cutoff_directional_bound (q₀ : ℝ) (hq₀ : 0 < q₀) (q β : Space) (K : ℕ) :
    |Well.directionalDerivative K (Well.chi q₀) q β| ≤
      (2 : ℝ)^45 * (((2 : ℝ)^16/q₀)*‖β‖)^K * (K.factorial : ℝ)^2 := by
  have hn : ‖NormedSpace.normalize β‖ ≤ 1 := by
    by_cases hz : β = 0
    · simp [hz]
    · exact (NormedSpace.norm_normalize hz).le
  have hb := Well.chi_directional_gevrey q₀ hq₀ q (NormedSpace.normalize β) hn K
  have he := directionalDerivative_smul K (Well.chi q₀) q (NormedSpace.normalize β) ‖β‖
  rw [NormedSpace.norm_smul_normalize] at he
  rw [he, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg β)]
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg β) K)).trans_eq
  rw [mul_pow]
  ring

def cutoffTaylor (K : ℕ) (q₀ : ℝ) (q β : Space) (s : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (K+1), coefficient j s *
    ((Well.directionalDerivative j (Well.chi q₀) q β : ℝ) : ℂ)

theorem cutoff_line_derivative (K : ℕ) (q₀ : ℝ) (q β : Space) (x : ℝ) :
    iteratedDeriv K (fun t : ℝ => Well.chi q₀ (q+t • β)) x =
      Well.directionalDerivative K (Well.chi q₀) (q+x • β) β := by
  rw [Well.directionalDerivative_eq_line K (Well.chi q₀) (Well.chi_contDiff q₀)]
  have he : (fun t : ℝ => Well.chi q₀ ((q+x • β)+t • β)) =
      (fun t : ℝ => (fun w : ℝ => Well.chi q₀ (q+w • β)) (x+t)) := by
    funext t
    dsimp only
    rw [add_smul, add_assoc]
  rw [he, iteratedDeriv_comp_const_add K (fun t : ℝ => Well.chi q₀ (q+t • β)) x]
  dsimp only
  rw [add_zero]

theorem cutoffTaylor_eq_taylor (K : ℕ) (q₀ : ℝ) (q β : Space) (x s : ℝ) :
    cutoffTaylor K q₀ (q+x • β) β s =
      taylor K (fun t : ℝ => Well.chi q₀ (q+t • β)) x s := by
  unfold cutoffTaylor taylor
  apply Finset.sum_congr rfl
  intro j _
  rw [cutoff_line_derivative]

theorem cutoffTaylor_defect (K : ℕ) (q₀ : ℝ) (q β : Space) (s : ℝ) :
    deriv (fun t : ℝ => cutoffTaylor K q₀ q β t) s -
      I * deriv (fun t : ℝ => cutoffTaylor K q₀ (q+t • β) β s) 0 =
        -I * coefficient K s *
          ((Well.directionalDerivative (K+1) (Well.chi q₀) q β : ℝ) : ℂ) := by
  have hzero (t : ℝ) : cutoffTaylor K q₀ q β t =
      taylor K (fun x : ℝ => Well.chi q₀ (q+x • β)) 0 t := by
    simpa only [zero_smul, add_zero] using cutoffTaylor_eq_taylor K q₀ q β 0 t
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Well.chi q₀ (q+t • β)) :=
    (Well.chi_contDiff q₀).comp (by fun_prop)
  simp_rw [hzero, cutoffTaylor_eq_taylor]
  rw [taylor_defect K _ hf, cutoff_line_derivative, zero_smul, add_zero]

theorem cutoffTaylor_defect_bound (K : ℕ) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (q β : Space) {s : ℝ} (hs : |s| ≤ 1) :
    ‖deriv (fun t : ℝ => cutoffTaylor K q₀ q β t) s -
      I * deriv (fun t : ℝ => cutoffTaylor K q₀ (q+t • β) β s) 0‖ ≤
      (2 : ℝ)^45 * (((2 : ℝ)^16/q₀)*‖β‖)^(K+1) *
        ((K+1).factorial : ℝ)^2 / (K.factorial : ℝ) := by
  rw [cutoffTaylor_defect, norm_mul, norm_mul, norm_neg, norm_I, one_mul,
    coefficient_norm, norm_real, Real.norm_eq_abs]
  have hc : |s|^K / (K.factorial : ℝ) ≤ 1 / (K.factorial : ℝ) := by
    gcongr
    exact pow_le_one₀ (abs_nonneg s) hs
  apply (mul_le_mul hc (cutoff_directional_bound q₀ hq₀ q β (K+1))
    (abs_nonneg _) (by positivity)).trans_eq
  ring

end Maxwell.Continuum.AlmostAnalytic
