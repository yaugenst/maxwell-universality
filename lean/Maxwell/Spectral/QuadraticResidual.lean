import Maxwell.Spectral.JetTransfer
import Maxwell.Spectral.Trial

namespace Maxwell.Spectral.QuadraticResidual

noncomputable section

variable {ι H V : Type*} [Fintype ι]
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem weighted_sum_norm_sq (q : ι → ℝ) (v : ι → H) :
    ‖∑ i, (q i : ℂ) • v i‖^2 ≤ (∑ i, (q i)^2) * ∑ i, ‖v i‖^2 := by
  have ht : ‖∑ i, (q i : ℂ) • v i‖ ≤ ∑ i, |q i| * ‖v i‖ := by
    exact (norm_sum_le _ _).trans (le_of_eq (by simp [norm_smul]))
  calc
    _ ≤ (∑ i, |q i| * ‖v i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ ≤ (∑ i, |q i|^2) * ∑ i, ‖v i‖^2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |q i|) (fun i => ‖v i‖)
    _ = _ := by simp only [sq_abs]

variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A strict finite Gram margin survives the proved exact-frame and
corrector replacements. The numerical losses are evaluated explicitly. -/
theorem relative_bound_of_saved (R S : V →L[ℂ] H) (K L : V →L[ℂ] V) (r : ℝ)
    (hS : ‖S‖ ≤ 2 * r^2)
    (hRerror : ‖R - S‖ ≤ (1/1000000 : ℝ) * r^2)
    (hKerror : ‖K - L‖ ≤ (2/1000000 : ℝ) * r^2)
    (hsaved : ∀ x, ‖S x‖^2 ≤ (18/5 : ℝ) * r^2 * Complex.re (inner ℂ x (L x)) -
      (1/10000 : ℝ) * r^4 * ‖x‖^2)
    (x : V) : ‖R x‖^2 ≤ (18/5 : ℝ) * r^2 * Complex.re (inner ℂ x (K x)) := by
  have hSx : ‖S x‖ ≤ 2 * r^2 * ‖x‖ :=
    (S.le_opNorm x).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  have hDx : ‖(R-S) x‖ ≤ (1/1000000 : ℝ) * r^2 * ‖x‖ :=
    ((R-S).le_opNorm x).trans (mul_le_mul_of_nonneg_right hRerror (norm_nonneg _))
  have hRx : ‖R x‖ ≤ ‖S x‖ + (1/1000000 : ℝ) * r^2 * ‖x‖ := by
    have h := norm_add_le (S x) ((R-S) x)
    have he : S x + (R-S) x = R x := by simp
    rw [he] at h
    exact h.trans (add_le_add_right hDx _)
  have hsquare := pow_le_pow_left₀ (norm_nonneg (R x)) hRx 2
  have hcross := mul_le_mul_of_nonneg_right hSx
    (show 0 ≤ (2/1000000 : ℝ) * r^2 * ‖x‖ by positivity)
  have hquad := quadratic_le_add_of_norm_sub_le L K
    ((2/1000000 : ℝ) * r^2) (by simpa only [norm_sub_rev] using hKerror) x
  have hquad' := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ (18/5 : ℝ) * r^2 by positivity)
  have hp : 0 ≤ r^4 * ‖x‖^2 := by positivity
  have hs := hsaved x
  nlinarith only [hsquare, hcross, hquad', hp, hs]

end
end Maxwell.Spectral.QuadraticResidual
