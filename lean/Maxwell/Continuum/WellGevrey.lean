import Maxwell.Continuum.WellRealDeriv

/-! Uniform directional Gevrey estimates for the literal radial well and its square root. -/

noncomputable section

namespace Maxwell.Continuum.Well

open Set Metric Filter
open scoped Topology

theorem directionalDerivative_bound_inside (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (hc : 1 / 2 ≤ c)
    (hvalue : ∀ y : Space, ‖y‖ < 1 → f y = Real.exp (-c / (1 - ‖y‖ ^ 2)))
    (y v : Space) (hy : ‖y‖ < 1) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    |directionalDerivative K f y v| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  let s := 1 - ‖y‖ ^ 2
  let a := inner ℝ y v
  let b := ‖v‖ ^ 2
  have hs : 0 < s := by dsimp [s]; nlinarith [norm_nonneg y]
  have hs₁ : s ≤ 1 := by dsimp [s]; nlinarith [sq_nonneg ‖y‖]
  have ha : |a| ≤ 1 := by
    have habs := abs_real_inner_le_norm y v
    dsimp [a]
    calc
      |inner ℝ y v| ≤ ‖y‖ * ‖v‖ := habs
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hb : |b| ≤ 1 := by dsimp [b]; rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [norm_nonneg v]
  let F := complexLineBump c s a b
  have he : (fun t : ℝ => f (y + t • v)) =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => (F t).re) := by
    have hn : Continuous (fun t : ℝ => ‖y + t • v‖) := by fun_prop
    have hm : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖y + t • v‖ < 1 :=
      hn.continuousAt.eventually (eventually_lt_nhds (by simpa using hy))
    filter_upwards [hm] with t ht
    rw [hvalue _ ht]
    dsimp [F]
    rw [complexLineBump_real, norm_line_sq]
    congr 2
    dsimp [s, a, b]
    ring
  have han : AnalyticOnNhd ℂ F (ball (0 : ℂ) (s / 100)) :=
    (complexLineBump_diffContOnCl c s a b hs hs₁ ha hb).1.analyticOnNhd isOpen_ball
  rw [directionalDerivative_eq_line K f hf y v, he.iteratedDeriv_eq K,
    iteratedDeriv_real_of_complex F _ isOpen_ball han K 0 (by simpa using (show 0 < s / 100 by positivity))]
  exact (Complex.abs_re_le_norm _).trans (complexLineBump_gevrey c s a b hc hs hs₁ ha hb K)

/-- Interior estimates extend to the unit sphere by continuity of the actual derivatives. -/
theorem directionalDerivative_bound (f : Space → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (hc : 1 / 2 ≤ c)
    (hvalue : ∀ y : Space, ‖y‖ < 1 → f y = Real.exp (-c / (1 - ‖y‖ ^ 2)))
    (hzero : ∀ y : Space, 1 < ‖y‖ → f y = 0)
    (y v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    |directionalDerivative K f y v| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  by_cases hy : ‖y‖ ≤ 1
  · have hclosed : IsClosed {z : Space |
        |directionalDerivative K f z v| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2} :=
      isClosed_le (directionalDerivative_continuous K f hf v).abs continuous_const
    have hsub : ball (0 : Space) 1 ⊆ {z : Space |
        |directionalDerivative K f z v| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2} := by
      intro z hz
      exact directionalDerivative_bound_inside f hf c hc hvalue z v (by simpa using hz) hv K
    have hmem : y ∈ closure (ball (0 : Space) 1) := by
      rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
      simpa using hy
    exact closure_minimal hsub hclosed hmem
  · have hgt : 1 < ‖y‖ := lt_of_not_ge hy
    have he : f =ᶠ[𝓝 y] (fun _ : Space => (0 : ℝ)) := by
      have hm : ∀ᶠ z : Space in 𝓝 y, 1 < ‖z‖ :=
        continuous_norm.continuousAt.eventually (eventually_gt_nhds hgt)
      filter_upwards [hm] with z hz
      exact hzero z hz
    have hd := (he.iteratedFDeriv (𝕜 := ℝ) K).eq_of_nhds
    rw [directionalDerivative, hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply, abs_zero]
    positivity

theorem w_directional_gevrey (y v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    |directionalDerivative K w y v| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  apply directionalDerivative_bound w w_contDiff 1 (by norm_num)
  · intro z hz
    exact ite_eq_left hz
  · intro z hz
    exact (w_zero_iff z).mpr hz.le
  · exact hv

theorem qw_directional_gevrey (y v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    |directionalDerivative K qw y v| ≤ (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  apply directionalDerivative_bound qw qw_contDiff (1 / 2) le_rfl
  · intro z hz
    simp only [qw, w, ite_eq_left hz, ← Real.exp_half]
    congr 1
    ring
  · intro z hz
    exact (qw_zero_iff z).mpr hz.le
  · exact hv

/-- The displayed derivative majorant in the continuum manuscript. -/
theorem well_directional_gevrey (y v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    |directionalDerivative K w y v| + |directionalDerivative K qw y v| ≤
      2 * (1024 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  have hw := w_directional_gevrey y v hv K
  have hq := qw_directional_gevrey y v hv K
  have hp : (400 : ℝ) ^ K ≤ 1024 ^ K := by gcongr; norm_num
  have hm : (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 ≤
      (1024 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by gcongr
  linarith

end Maxwell.Continuum.Well
