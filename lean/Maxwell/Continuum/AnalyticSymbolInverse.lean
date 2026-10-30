import Maxwell.Continuum.CauchyBounds

/-! A quantitative zero-free complex disk from a lower bound at its
real center and an actual analytic quadratic-order bound. Cauchy's
formula then controls every derivative of the reciprocal. -/

noncomputable section

namespace Maxwell.Continuum.AnalyticSymbolInverse

open Set Metric

theorem variation_bound {f : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (2*R)))
    (hbound : ∀ ζ ∈ closedBall 0 (2*R), ‖f ζ‖ ≤ C*R^2)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ R) : ‖f ζ-f 0‖ ≤ C*R*‖ζ‖ := by
  have hd (w : ℂ) (hw : w ∈ closedBall 0 R) : ‖deriv f w‖ ≤ C*R := by
    have hw' : ‖w‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hw
    exact (CauchyBounds.norm_deriv_le hf hbound hR (by linarith)).trans_eq
      (by field_simp [hR.ne'])
  simpa only [sub_zero] using
    (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hf w (closedBall_subset_closedBall (by linarith) hw)).differentiableAt)
      hd (show (0 : ℂ) ∈ closedBall 0 R by simpa using hR.le)
      (show ζ ∈ closedBall 0 R by simpa only [mem_closedBall, dist_zero_right] using hζ)

theorem denominator_lower {f : ℂ → ℂ} {R C a : ℝ}
    (hR : 0 < R) (hC : 0 < C) (ha : 0 < a) (haC : a ≤ 2*C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (2*R)))
    (hbound : ∀ ζ ∈ closedBall 0 (2*R), ‖f ζ‖ ≤ C*R^2)
    (hlower : a*R^2 ≤ ‖f 0‖)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ (a/(2*C))*R) : a*R^2/2 ≤ ‖f ζ‖ := by
  have he : a/(2*C) ≤ 1 := (div_le_one (by positivity)).mpr haC
  have hζR : ‖ζ‖ ≤ R := hζ.trans
    ((mul_le_mul_of_nonneg_right he hR.le).trans_eq (one_mul _))
  have hd := variation_bound hR hf hbound hζR
  have hm := mul_le_mul_of_nonneg_left hζ (mul_pos hC hR).le
  have hc : C*R*((a/(2*C))*R) = a*R^2/2 := by field_simp [hC.ne']
  rw [hc] at hm
  have ht := norm_sub_le (f ζ) (f ζ-f 0)
  rw [sub_sub_cancel] at ht
  linarith only [hlower, ht, hd, hm]

theorem reciprocal_bound {f : ℂ → ℂ} {R C a : ℝ}
    (hR : 0 < R) (hC : 0 < C) (ha : 0 < a) (haC : a ≤ 2*C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (2*R)))
    (hbound : ∀ ζ ∈ closedBall 0 (2*R), ‖f ζ‖ ≤ C*R^2)
    (hlower : a*R^2 ≤ ‖f 0‖)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ (a/(2*C))*R) : ‖(f ζ)⁻¹‖ ≤ 2/(a*R^2) := by
  rw [norm_inv]
  exact (inv_anti₀ (by positivity : 0 < a*R^2/2)
    (denominator_lower hR hC ha haC hf hbound hlower hζ)).trans_eq (by ring)

theorem reciprocal_analytic {f : ℂ → ℂ} {R C a : ℝ}
    (hR : 0 < R) (hC : 0 < C) (ha : 0 < a) (haC : a ≤ 2*C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (2*R)))
    (hbound : ∀ ζ ∈ closedBall 0 (2*R), ‖f ζ‖ ≤ C*R^2)
    (hlower : a*R^2 ≤ ‖f 0‖) :
    AnalyticOnNhd ℂ (fun ζ => (f ζ)⁻¹) (closedBall 0 ((a/(2*C))*R)) := by
  intro ζ hζ
  have hζ' : ‖ζ‖ ≤ (a/(2*C))*R := by simpa only [mem_closedBall, dist_zero_right] using hζ
  have he : a/(2*C) ≤ 1 := (div_le_one (by positivity)).mpr haC
  have hζR : ‖ζ‖ ≤ 2*R := hζ'.trans (by nlinarith only [he, hR])
  apply (hf ζ (by simpa only [mem_closedBall, dist_zero_right] using hζR)).inv
  apply norm_pos_iff.mp
  exact (by positivity : 0 < a*R^2/2).trans_le
    (denominator_lower hR hC ha haC hf hbound hlower hζ')

theorem reciprocal_iteratedDeriv {f : ℂ → ℂ} {R C a : ℝ}
    (hR : 0 < R) (hC : 0 < C) (ha : 0 < a) (haC : a ≤ 2*C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (2*R)))
    (hbound : ∀ ζ ∈ closedBall 0 (2*R), ‖f ζ‖ ≤ C*R^2)
    (hlower : a*R^2 ≤ ‖f 0‖) (n : ℕ) :
    ‖iteratedDeriv n (fun ζ => (f ζ)⁻¹) 0‖ ≤
      (n.factorial : ℝ)*(2/(a*R^2))/(((a/(2*C))*R)^n) := by
  apply CauchyBounds.norm_iteratedDeriv_le n
    (reciprocal_analytic hR hC ha haC hf hbound hlower)
    (fun ζ hζ => reciprocal_bound hR hC ha haC hf hbound hlower
      (by simpa only [mem_closedBall, dist_zero_right] using hζ))
    (by positivity)
  simp only [norm_zero, zero_add, le_refl]

end Maxwell.Continuum.AnalyticSymbolInverse
