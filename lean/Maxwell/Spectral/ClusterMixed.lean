import Maxwell.Spectral.InfiniteNorm
import Maxwell.Spectral.Trial

namespace Maxwell.Spectral.ClusterMixed

noncomputable section

variable {H V : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The exact corrector equation makes the effective quadratic coefficient
Hermitian, even when the center eigenvalues are distinct. -/
theorem effective_selfAdjoint (A₀ A₁ A₂ : H →L[ℂ] H)
    (h₀ : IsSelfAdjoint A₀) (h₁ : IsSelfAdjoint A₁) (h₂ : IsSelfAdjoint A₂)
    (Φ Y : V →L[ℂ] H) (hcancel : A₀.comp Y = A₁.comp Φ) :
    IsSelfAdjoint (Φ.adjoint.comp (A₂.comp Φ) - Φ.adjoint.comp (A₁.comp Y)) := by
  have h0 : A₀.adjoint = A₀ := h₀
  have h1 : A₁.adjoint = A₁ := h₁
  have h2 : A₂.adjoint = A₂ := h₂
  have hcross : Φ.adjoint.comp (A₁.comp Y) = Y.adjoint.comp (A₀.comp Y) := by
    have h := congrArg (fun L : V →L[ℂ] H => L.adjoint.comp Y) hcancel
    simpa only [ContinuousLinearMap.adjoint_comp, h0, h1,
      ContinuousLinearMap.comp_assoc] using h.symm
  rw [hcross]
  change (Φ.adjoint.comp (A₂.comp Φ) - Y.adjoint.comp (A₀.comp Y)).adjoint = _
  simp only [map_sub, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    h0, h2, ContinuousLinearMap.comp_assoc]

/-- A positive effective coefficient with its certified quadratic upper
bound has the corresponding true Hilbert operator-norm bound. -/
theorem effective_norm_le (K : V →L[ℂ] V) (hK : IsSelfAdjoint K)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hlo : ∀ x, 0 ≤ Complex.re (inner ℂ x (K x)))
    (hhi : ∀ x, Complex.re (inner ℂ x (K x)) ≤ κ * ‖x‖ ^ 2) : ‖K‖ ≤ κ := by
  apply selfAdjoint_norm_le_of_quadratic K hK κ hκ
  intro x
  have hl := hlo x
  have hh := hhi x
  rw [inner_re_symm]
  change |Complex.re (inner ℂ x (K x))| ≤ _
  rwa [abs_of_nonneg hl]

/-- Exact center invariance and the compressed coefficient norm imply the
mixed center-offset bound in the local residual square. -/
theorem mixed_offset_bound (Φ D R : V →L[ℂ] H) (δ κ : ℝ)
    (hδ : 0 ≤ δ) (hΦ : ‖Φ‖ ≤ 1)
    (hD : ‖D‖ ≤ δ) (hK : ‖Φ.adjoint.comp R‖ ≤ κ)
    (hinvariant : Φ.comp (Φ.adjoint.comp D) = D) (x : V) :
    Complex.re (inner ℂ (D x) (R x)) ≤ δ * κ * ‖x‖ ^ 2 := by
  have hrepr : D x = Φ (Φ.adjoint (D x)) := by
    exact (congrArg (fun L : V →L[ℂ] H => L x) hinvariant).symm
  have hadj : ‖Φ.adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hΦ
  have hDx : ‖Φ.adjoint (D x)‖ ≤ δ * ‖x‖ := by
    calc
      _ ≤ ‖Φ.adjoint‖ * ‖D x‖ := Φ.adjoint.le_opNorm _
      _ ≤ 1 * (δ * ‖x‖) := mul_le_mul hadj
        ((D.le_opNorm x).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg x)))
        (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hKx : ‖Φ.adjoint (R x)‖ ≤ κ * ‖x‖ :=
    ((Φ.adjoint.comp R).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hK (norm_nonneg x))
  calc
    _ = Complex.re (inner ℂ (Φ.adjoint (D x)) (Φ.adjoint (R x))) := by
      conv_lhs => arg 1; lhs; rw [hrepr]
      rw [Φ.adjoint_inner_right]
    _ ≤ ‖inner ℂ (Φ.adjoint (D x)) (Φ.adjoint (R x))‖ := Complex.re_le_norm _
    _ ≤ ‖Φ.adjoint (D x)‖ * ‖Φ.adjoint (R x)‖ := norm_inner_le_norm _ _
    _ ≤ (δ * ‖x‖) * (κ * ‖x‖) :=
      mul_le_mul hDx hKx (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))
    _ = _ := by ring

end
end Maxwell.Spectral.ClusterMixed
