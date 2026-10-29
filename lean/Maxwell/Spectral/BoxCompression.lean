import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace Maxwell.Spectral.BoxCompression

noncomputable section
variable {H V W : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def sandwich (D : H →L[ℂ] H) (A : V →L[ℂ] H) (B : W →L[ℂ] H) : W →L[ℂ] V :=
  A.adjoint.comp (D.comp B)

theorem sandwich_norm (D : H →L[ℂ] H) (A : V →L[ℂ] H) (B : W →L[ℂ] H)
    (hD : ‖D‖ ≤ 1) : ‖sandwich D A B‖ ≤ ‖A‖ * ‖B‖ := by
  calc
    _ ≤ ‖A.adjoint‖ * ‖D.comp B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A.adjoint‖ * (‖D‖ * ‖B‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * ‖B‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      nlinarith [mul_le_mul_of_nonneg_left hD (norm_nonneg A), norm_nonneg B]

theorem diagonal_remainder_identity (D : H →L[ℂ] H)
    (A₀ A₁ Δ : V →L[ℂ] H) :
    sandwich D (A₀+Δ) (A₀+Δ) - sandwich D A₀ A₀ -
        (sandwich D A₁ A₀ + sandwich D A₀ A₁) =
      sandwich D (Δ-A₁) A₀ + sandwich D A₀ (Δ-A₁) + sandwich D Δ Δ := by
  simp only [sandwich, map_add, map_sub, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_sub]
  module

/-- The exact magnetic compression remainder used in both signed diagonal
tests: `s² (ν e + ν²)`. It uses the norm of the center curl applied to the
witness, rather than the global curl norm. -/
theorem diagonal_remainder_bound (D : H →L[ℂ] H)
    (A₀ A₁ Δ : V →L[ℂ] H) (s ν e : ℝ)
    (hs : 0 ≤ s) (hν : 0 ≤ ν) (he : 0 ≤ e) (hD : ‖D‖ ≤ 1)
    (hA₀ : ‖A₀‖ ≤ e) (hΔ : ‖Δ‖ ≤ s*ν) (hR : ‖Δ-A₁‖ ≤ s^2*ν/2) :
    ‖sandwich D (A₀+Δ) (A₀+Δ) - sandwich D A₀ A₀ -
        (sandwich D A₁ A₀ + sandwich D A₀ A₁)‖ ≤ s^2*(ν*e+ν^2) := by
  rw [diagonal_remainder_identity]
  calc
    _ ≤ ‖sandwich D (Δ-A₁) A₀‖ + ‖sandwich D A₀ (Δ-A₁)‖ +
        ‖sandwich D Δ Δ‖ := (norm_add_le _ _).trans
      (add_le_add_left (norm_add_le _ _) _)
    _ ≤ ‖Δ-A₁‖*‖A₀‖ + ‖A₀‖*‖Δ-A₁‖ + ‖Δ‖*‖Δ‖ := by
      gcongr <;> exact sandwich_norm _ _ _ hD
    _ ≤ (s^2*ν/2)*e + e*(s^2*ν/2) + (s*ν)*(s*ν) := by gcongr
    _ = _ := by ring

theorem mixed_remainder_identity (D : H →L[ℂ] H)
    (A₀ ΔA : V →L[ℂ] H) (B₁ ΔB : W →L[ℂ] H) :
    sandwich D (A₀+ΔA) ΔB - sandwich D A₀ B₁ =
      sandwich D A₀ (ΔB-B₁) + sandwich D ΔA ΔB := by
  simp only [sandwich, map_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_sub]
  module

/-- The low-gradient center curl vanishes, giving the mixed remainder
`ν_G s² (e/2+ν)`; the actual gradient witness has `ν_G=8`. -/
theorem mixed_remainder_bound (D : H →L[ℂ] H)
    (A₀ ΔA : V →L[ℂ] H) (B₁ ΔB : W →L[ℂ] H) (s ν e νG : ℝ)
    (hs : 0 ≤ s) (hν : 0 ≤ ν) (he : 0 ≤ e) (_hνG : 0 ≤ νG) (hD : ‖D‖ ≤ 1)
    (hA₀ : ‖A₀‖ ≤ e) (hΔA : ‖ΔA‖ ≤ s*ν) (hΔB : ‖ΔB‖ ≤ s*νG)
    (hR : ‖ΔB-B₁‖ ≤ s^2*νG/2) :
    ‖sandwich D (A₀+ΔA) ΔB - sandwich D A₀ B₁‖ ≤ νG*s^2*(e/2+ν) := by
  rw [mixed_remainder_identity]
  calc
    _ ≤ ‖sandwich D A₀ (ΔB-B₁)‖ + ‖sandwich D ΔA ΔB‖ := norm_add_le _ _
    _ ≤ ‖A₀‖*‖ΔB-B₁‖ + ‖ΔA‖*‖ΔB‖ := by
      gcongr <;> exact sandwich_norm _ _ _ hD
    _ ≤ e*(s^2*νG/2) + (s*ν)*(s*νG) := by gcongr
    _ = _ := by ring

end
end Maxwell.Spectral.BoxCompression
